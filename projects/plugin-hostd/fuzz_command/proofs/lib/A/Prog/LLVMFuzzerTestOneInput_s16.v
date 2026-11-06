(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the kit of segment A of LLVMFuzzerTestOneInput's ASan walk (plugin-hostd/fuzz_command, 0x8653c .. 0x865f0): the symbolic state after the first rec_clear and its seed, the image words the segment reads as cmd_ro_ok has them, the recorder after the memset of g_rec.state and g_rec.host_settings, and the eleven frame words of the loop head read off the symbolic state, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (cl_seedX: the seed of a point inside a function) and A/ACh7.v (the keep lemmas of a segment). *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05 YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import ACfn AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaLibF PaLibG PaSB CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdBase CmdRep CmdObj CmdRo CmdAddr CmdChk
  CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_clear_c send_message_c check_reply_c check_arity_c check_words_c check_refusal_c check_round_trip_c
verbs_receive_c LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Local Open Scope Z_scope.

(* ---- the symbolic state at 0x8653c (LO_RC1RA), after the first rec_clear ---- *)
(* rec_ncodes, the code count's address (GOT 0xa7070); rec_codes is the listing's object A_OBJ 40, g_rec A_OBJ 44 *)
Definition LA_NC : Z := 0x21cc0.
(* the shadow base is s1 (atom 9); atom 32 is rec_ncodes' address *)
Definition LAx : sv := SOff 9 0.
Definition LAspan : Z * Z := (LT_SB, LT_SB + 2 ^ 44 - 1).
(* the eleven frame words at sp + 0 .. sp + 88 the segment writes; the three GOT words it loads (0xa7068 g_rec,
   0xa7070 rec_ncodes, 0xa7078 rec_codes) and rec_ncodes' word *)
Definition la_frame : YP09.region := YP09.mkRegion (Some 2%nat) 0 88 0 88 [].
Definition la_ncodes : YP09.region := YP09.mkRegion (Some 32%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit 58))].
Definition la_regions : smem :=
  [la_frame; obj8_region 2 (SOff (A_OBJ 44) 0); obj8_region 3 (SOff 32 0); obj8_region 4 (SOff (A_OBJ 40) 0);
   la_ncodes].
Definition la_facts : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (9%nat, mkAF LT_SB LT_SB 0); (32%nat, mkAF LA_NC LA_NC 6);
    (A_OBJ 44, mkAF A_G_REC A_G_REC 6); (A_OBJ 40, mkAF LT_CODES LT_CODES 5) ] [] [].
Definition ss_la : sstate := mkSS LO_RC1RA sr_atoms la_regions None la_facts.
(* the one inline check of the segment, rec_ncodes' load (0x8656c), vanishes by this shadow entry *)
Definition la_SH : list shent := [mkSHE 32 0 4].
Definition la_extra : list word := [Z_to_bv 64 LA_NC].

(* ---- byte vocabulary ---- *)
Lemma la_val_of_aval : forall segs H (mem : word -> option byte) a n v,
  aval_mem (aview segs H mem) a n v -> val_mem segs (mrestrict H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte segs (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Eb; cbn in Hv; [|discriminate Hv].
injection Hv as Hb. rewrite <- (Z_to_bv_bv_unsigned 8 b). rewrite Hb. reflexivity.
Qed.
Lemma la_aval_of_bytes : forall rd a l n v, abytes_atR rd a l -> length l = n ->
  (forall k, (k < n)%nat -> bv_unsigned (nth k l (Z_to_bv 8 0)) = YG0f.le_byte v n k) -> aval_mem rd a n v.
Proof. intros rd a l n v H Hl Hk k Hkn. rewrite (H k) by (rewrite Hl; exact Hkn). f_equal. exact (Hk k Hkn). Qed.
Lemma la_aval_kept : forall (rd rd' : reader) a n v, aval_mem rd a n v ->
  (forall k, (k < n)%nat -> rd' (a + Z.of_nat k) = rd (a + Z.of_nat k)) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H Hk i Hi. rewrite (Hk i Hi). exact (H i Hi). Qed.
Lemma la_le_byte_zero : forall n k, YG0f.le_byte 0 n k = 0.
Proof.
intros n k. unfold YG0f.le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia).
rewrite Z.shiftr_0_l. apply Z.mod_0_l. lia.
Qed.

(* ---- the image words the segment reads, as cmd_ro_ok has them ---- *)
Lemma la_ro_bytes : forall rd, cmd_ro_ok rd ->
  abytes_atR rd 0xa7068 RO_ptr_a7068 /\ abytes_atR rd 0xa7070 RO_ptr_a7070 /\
  abytes_atR rd 0xa7078 RO_ptr_a7078 /\ abytes_atR rd 0x21cc0 RO_rec_ncodes.
Proof.
intros rd [HRO _]. unfold cmd_ro_bytes in HRO.
split; [|split; [|split]]; clear - HRO.
- repeat match type of HRO with abytes_atR _ 0xa7068 _ /\ _ => exact (proj1 HRO) | _ /\ _ => apply proj2 in HRO end.
- repeat match type of HRO with abytes_atR _ 0xa7070 _ /\ _ => exact (proj1 HRO) | _ /\ _ => apply proj2 in HRO end.
- repeat match type of HRO with abytes_atR _ 0xa7078 _ /\ _ => exact (proj1 HRO) | _ /\ _ => apply proj2 in HRO end.
- repeat match type of HRO with abytes_atR _ 0x21cc0 _ /\ _ => exact (proj1 HRO) | _ /\ _ => apply proj2 in HRO end.
Qed.
Lemma la_ro_vals : forall rd, cmd_ro_ok rd ->
  aval_mem rd 0xa7068 8 A_G_REC /\ aval_mem rd 0xa7070 8 LA_NC /\ aval_mem rd 0xa7078 8 LT_CODES /\
  aval_mem rd LA_NC 4 LT_NCODES.
Proof.
intros rd H. destruct (la_ro_bytes rd H) as (H1 & H2 & H3 & H4).
split; [|split; [|split]].
- apply (la_aval_of_bytes _ _ _ 8%nat _ H1 eq_refl). intros k Hk. do 8 (destruct k as [|k]; [vm_compute; reflexivity|]). exfalso; clear - Hk; lia.
- apply (la_aval_of_bytes _ _ _ 8%nat _ H2 eq_refl). intros k Hk. do 8 (destruct k as [|k]; [vm_compute; reflexivity|]). exfalso; clear - Hk; lia.
- apply (la_aval_of_bytes _ _ _ 8%nat _ H3 eq_refl). intros k Hk. do 8 (destruct k as [|k]; [vm_compute; reflexivity|]). exfalso; clear - Hk; lia.
- apply (la_aval_of_bytes _ _ _ 4%nat _ H4 eq_refl). intros k Hk. do 4 (destruct k as [|k]; [vm_compute; reflexivity|]). exfalso; clear - Hk; lia.
Qed.
(* ---- the recorder after the memset: g_rec.state = g_rec.host_settings = 0 ---- *)
Definition lt_Rz (R : rstate) : rstate :=
  RState (r_refuse R) (r_code R) (r_calls R) (r_spill R) (r_answer R) (r_nreplies R) (r_reply R) 0 0.
Lemma lt_Rz_rkey : forall R, r_calls R = [] -> r_spill R = (0, []) -> rkey (lt_Rz R) = rkey R_ENTRY.
Proof. intros R Hc Hs. unfold rkey, lt_Rz, R_ENTRY. cbn [r_calls r_spill r_state r_host]. rewrite Hc, Hs. reflexivity. Qed.
Local Ltac oz := unfold A_G_REC, A_REC_SPILL, OFF_STATE, SC_SIZE, OFF_NCALLS, OFF_ANSWER, OFF_REPLY, OFF_REPLY_SIZE,
  OFF_REFUSE, OFF_CODE, OFF_NREPLIES, CALL_OFF_FN, CALL_OFF_NARGS; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
Lemma la_arep_zero : forall bl (rd rd' : reader) R Q,
  arep_at bl rd A_G_REC A_REC_SPILL R Q -> r_calls R = [] -> r_answer R = None -> r_reply R = None ->
  r_spill R = (0, []) ->
  (forall a, A_G_REC <= a < A_G_REC + OFF_STATE -> rd' a = rd a) ->
  (forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> rd' a = rd a) ->
  (forall i, 0 <= i < 16 -> rd' (A_G_REC + OFF_STATE + i) = Some 0) ->
  arep_at bl rd' A_G_REC A_REC_SPILL (lt_Rz R) Q.
Proof.
intros bl rd rd' [rf cd cs sp an nr rp st ho] Q HA Hc Ha Hr Hsp KG KS Z16.
cbn [r_calls r_answer r_reply r_spill] in Hc, Ha, Hr, Hsp. subst cs an rp sp. unfold lt_Rz. cbn [r_refuse r_code r_calls r_spill
  r_answer r_nreplies r_reply r_state r_host].
destruct HA as (Hg & Hs & Hap & (H16 & HlQ & Vnc & HC & Hspl & HFs) & Hans & Hrep &
  (V0 & V4 & V920 & V944 & V952 & Rr & Rc & Rn & Rs & Rh) & Hown).
cbn [r_calls r_spill r_answer r_reply r_refuse r_code r_nreplies r_state r_host fst snd] in *.
assert (KG' : forall a n v, aval_mem rd a n v -> A_G_REC <= a -> a + Z.of_nat n <= A_G_REC + OFF_STATE ->
  aval_mem rd' a n v).
{ intros a n v H Ha1 Ha2 k Hk. rewrite KG by lia. exact (H k Hk). }
assert (KS' : forall a n v, aval_mem rd a n v -> A_REC_SPILL <= a -> a + Z.of_nat n <= A_REC_SPILL + SC_SIZE ->
  aval_mem rd' a n v).
{ intros a n v H Ha1 Ha2 k Hk. rewrite KS by lia. exact (H k Hk). }
assert (Z8 : forall o, 0 <= o -> o + 8 <= 16 -> aval_mem rd' (A_G_REC + OFF_STATE + o) 8 0).
{ intros o Ho1 Ho2 k Hk. rewrite la_le_byte_zero.
  replace (A_G_REC + OFF_STATE + o + Z.of_nat k) with (A_G_REC + OFF_STATE + (o + Z.of_nat k)) by lia.
  apply Z16. lia. }
assert (ZS : aval_mem rd' (A_G_REC + OFF_STATE) 8 0)
  by (replace (A_G_REC + OFF_STATE) with (A_G_REC + OFF_STATE + 0) by lia; apply Z8; lia).
assert (ZH : aval_mem rd' (A_G_REC + OFF_HOST) 8 0)
  by (replace (A_G_REC + OFF_HOST) with (A_G_REC + OFF_STATE + 8) by (unfold OFF_HOST, OFF_STATE; lia); apply Z8; lia).
assert (EA : l_answer Q = None) by (unfold aanswer_at in Hans; destruct (l_answer Q); [destruct Hans | reflexivity]).
assert (ER : l_reply Q = None) by (unfold areply_at in Hrep; destruct (l_reply Q); [destruct Hrep | reflexivity]).
rewrite EA in Hans. rewrite ER in Hrep. cbn [aanswer_at areply_at] in Hans, Hrep.
destruct Hrep as [Hr1 Hr2]. destruct Hspl as (S1 & S2 & S3 & S4 & S5 & S6 & S7).
unfold arep_at, ag1_calls, acall_at, ag1_scalars. rewrite EA, ER. cbn [aanswer_at areply_at].
cbn [r_calls r_spill r_answer r_reply r_refuse r_code r_nreplies r_state r_host fst snd].
split; [exact Hg|]. split; [exact Hs|]. split; [exact Hap|].
split; [|split; [|split; [|split]]].
- split; [exact H16|]. split; [exact HlQ|]. split; [apply KG'; [exact Vnc | oz | oz]|].
  split; [intros i c P Hi; destruct i; discriminate Hi|].
  split; [|exact HFs].
  split; [exact S1|]. split; [exact S2|]. split; [exact S3|].
  split; [apply KS'; [exact S4 | oz | oz]|]. split; [apply KS'; [exact S5 | oz | oz]|].
  split; [exact S6|]. intros k s pn Hk. destruct k; discriminate Hk.
- apply KG'; [exact Hans | oz | oz].
- split; [apply KG'; [exact Hr1 | oz | oz] | apply KG'; [exact Hr2 | oz | oz]].
- split; [apply KG'; [exact V0 | oz | oz]|]. split; [apply KG'; [exact V4 | oz | oz]|].
  split; [apply KG'; [exact V920 | oz | oz]|]. split; [exact ZS|]. split; [exact ZH|]. lia.
- exact Hown.
Qed.

(* the frame words of the loop head as the symbolic run leaves them (0x8654c .. 0x865f0), in the order it writes them *)
Definition la_slot_cs : list YP09.chunk :=
  [YP09.mkChunk 32 (CVal 8 (SOff 285 0)); YP09.mkChunk 16 (CVal 8 (SLit 7));
   YP09.mkChunk 40 (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 285 4) (SLit 3)) (SOff 9 0)));
   YP09.mkChunk 48 (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 285 952) (SLit 3)) (SOff 9 0)));
   YP09.mkChunk 0 (CVal 8 (SOff 285 4)); YP09.mkChunk 56 (CVal 8 (SOff 281 0));
   YP09.mkChunk 64 (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 285 0) (SLit 3)) (SOff 9 0)));
   YP09.mkChunk 8 (CVal 8 (SOff 285 952));
   YP09.mkChunk 72 (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 285 944) (SLit 3)) (SOff 9 0)));
   YP09.mkChunk 80 (CVal 8 (SLit 58)); YP09.mkChunk 24 (CVal 8 (SOff 285 944))].
(* the value of an 8-byte chunk *)
Lemma la_den_off : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
  bv_unsigned (sv_denot E (SOff n c)) mod 2 ^ (8 * Z.of_N 8) = v + c.
Proof.
intros E n v c H Hv Hc. change (bv_unsigned (sv_denot E (SOff n c))) with (U E (SOff n c)).
rewrite (U_atom_off E n v c H Hv Hc). apply Z.mod_small. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact Hc.
Qed.
Lemma la_den_lit : forall E z, 0 <= z < 2 ^ 64 -> bv_unsigned (sv_denot E (SLit z)) mod 2 ^ (8 * Z.of_N 8) = z.
Proof.
intros E z Hz. change (bv_unsigned (sv_denot E (SLit z))) with (U E (SLit z)). rewrite (U_lit E z Hz).
apply Z.mod_small. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact Hz.
Qed.
Lemma la_den_shx : forall E n m c v sb, ew E n = Z_to_bv 64 v -> ew E m = Z_to_bv 64 sb -> 0 <= v -> 0 <= c ->
  v + c < 2 ^ 63 -> 0 <= sb < 2 ^ 32 ->
  bv_unsigned (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff m 0))) mod 2 ^ (8 * Z.of_N 8) =
  sb + (v + c) / 8.
Proof.
intros E n m c v sb Hn Hm Hv Hc Hvc Hsb. rewrite (denot_shx E n m c v sb Hn Hm Hv Hc Hvc Hsb).
pose proof (Z.div_pos (v + c) 8 ltac:(lia) ltac:(lia)) as D1.
pose proof (Z.div_lt_upper_bound (v + c) 8 (2 ^ 60) ltac:(lia) ltac:(lia)) as D2.
rewrite unsigned_lit_small by lia. apply Z.mod_small. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Definition la_E (regs : bvmap 5 word) : env := Eimg (Ereg regs la_extra).
Local Ltac la_in := unfold la_slot_cs; cbn [In]; repeat (first [left; reflexivity | right]).
(* the eleven frame words at the loop head (LT_SLOTS) from the frame region the run leaves *)
Lemma la_slots_of_region : forall E (W : world SEGS) mf sp,
  region_ok SEGS E (mrestrict (w_H W) mf) (YP09.mkRegion (Some 2%nat) 0 88 0 88 la_slot_cs) ->
  bv_unsigned (ew E 2) = sp ->
  ew E 285 = Z_to_bv 64 A_G_REC -> ew E 281 = Z_to_bv 64 LT_CODES -> ew E 9 = Z_to_bv 64 LT_SB ->
  forall o v, In (o, v) LT_SLOTS -> rdword (rdW W mf) (sp + o) = Some v.
Proof.
intros E W mf sp HR Hsp E285 E281 E9 o v Hin.
assert (FLD : forall od e v', In (YP09.mkChunk od (CVal 8 e)) la_slot_cs ->
  bv_unsigned (sv_denot E e) mod 2 ^ (8 * Z.of_N 8) = v' -> 0 <= v' < 2 ^ 64 -> rdword (rdW W mf) (sp + od) = Some v').
{ intros od e v' Hc He Hv. apply rdword_of_val_mem; [|exact Hv]. rewrite <- He.
  exact (field_of_region_any E _ 2%nat sp _ _ _ _ _ od 8 e HR Hsp Hc ltac:(cbn; lia)). }
assert (G0 : 0 <= A_G_REC < 2 ^ 40) by (unfold A_G_REC; lia).
assert (S0 : 0 <= LT_SB < 2 ^ 32) by (unfold LT_SB; lia).
unfold LT_SLOTS in Hin. cbn [In] in Hin.
destruct Hin as [Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[]]]]]]]]]]]]; injection Hq as <- <-.
- apply (FLD 0 (SOff 285 4)); [la_in | apply la_den_off; [exact E285 | lia | lia] | lia].
- apply (FLD 8 (SOff 285 952)); [la_in | apply la_den_off; [exact E285 | lia | lia] | lia].
- apply (FLD 16 (SLit 7)); [la_in | apply la_den_lit; lia | lia].
- apply (FLD 24 (SOff 285 944)); [la_in | apply la_den_off; [exact E285 | lia | lia] | lia].
- apply (FLD 32 (SOff 285 0)); [la_in | | lia].
  rewrite (la_den_off E 285 A_G_REC 0 E285 ltac:(lia) ltac:(lia)). apply Z.add_0_r.
- apply (FLD 40 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 285 4) (SLit 3)) (SOff 9 0))); [la_in | | ].
  + apply (la_den_shx E 285 9 4 A_G_REC LT_SB E285 E9); lia.
  + pose proof (Z.div_pos (A_G_REC + 4) 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound (A_G_REC + 4) 8 (2 ^ 40) ltac:(lia) ltac:(lia)). lia.
- apply (FLD 48 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 285 952) (SLit 3)) (SOff 9 0))); [la_in | | ].
  + apply (la_den_shx E 285 9 952 A_G_REC LT_SB E285 E9); lia.
  + pose proof (Z.div_pos (A_G_REC + 952) 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound (A_G_REC + 952) 8 (2 ^ 40) ltac:(lia) ltac:(lia)). lia.
- apply (FLD 56 (SOff 281 0)); [la_in | | unfold LT_CODES; lia].
  rewrite (la_den_off E 281 LT_CODES 0 E281 ltac:(unfold LT_CODES; lia) ltac:(unfold LT_CODES; lia)). apply Z.add_0_r.
- apply (FLD 64 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 285 0) (SLit 3)) (SOff 9 0))); [la_in | | ].
  + rewrite (la_den_shx E 285 9 0 A_G_REC LT_SB E285 E9) by lia. rewrite Z.add_0_r. reflexivity.
  + pose proof (Z.div_pos A_G_REC 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound A_G_REC 8 (2 ^ 40) ltac:(lia) ltac:(lia)). lia.
- apply (FLD 72 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 285 944) (SLit 3)) (SOff 9 0))); [la_in | | ].
  + apply (la_den_shx E 285 9 944 A_G_REC LT_SB E285 E9); lia.
  + pose proof (Z.div_pos (A_G_REC + 944) 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound (A_G_REC + 944) 8 (2 ^ 40) ltac:(lia) ltac:(lia)). lia.
- apply (FLD 80 (SLit 58)); [la_in | apply la_den_lit; unfold LT_NCODES; lia | unfold LT_NCODES; lia].
Qed.
(* the saved registers stay where the entry put them while the frame above sp + 88 is kept *)
Lemma la_saved_kept : forall (cx : lcx) (rd rd' : reader), lt_saved cx rd ->
  (forall a, x_sp0 cx - 104 <= a < x_sp0 cx -> rd' a = rd a) -> lt_saved cx rd'.
Proof.
intros cx rd rd' H K i r Hn.
assert (Hi : (i < length LT_SAVED)%nat) by (apply nth_error_Some; rewrite Hn; discriminate). cbn in Hi.
rewrite (rdword_ext rd rd'); [exact (H i r Hn)|]. intros k Hk. apply K. lia.
Qed.
Section e.
Variable B : asyms.
(* the per-binary facts *)
Hypothesis HB : CmdBSyms B.
Hypothesis VOBJS : cmd_val_objs.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.

(* the recorder of lt_rec after the memset, when g_rec below the two fields, record.spill and g_quitting are kept *)
Lemma la_rec_zero : forall cx ly S (W W' : world SEGS) mem mem' R,
  lt_rec B cx ly S W mem R [] 0 [] -> r_calls R = [] -> r_answer R = None -> r_reply R = None ->
  (forall a, (A_G_REC <= a < A_G_REC + OFF_STATE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE \/
     A_G_QUITTING <= a < A_G_QUITTING + 4) -> rdW W' mem' a = rdW W mem a) ->
  (forall i, 0 <= i < 16 -> rdW W' mem' (A_G_REC + OFF_STATE + i) = Some 0) ->
  lt_rec B cx ly S W' mem' (lt_Rz R) [] 0 [].
Proof.
intros cx ly S W W' mem mem' R ((Q & HA & HO) & Hsp & H2 & Hq & Rq & HP) Hc Ha Hr K Z16.
unfold lt_rec, rec_repA.
split; [|split; [exact Hsp|split; [exact H2|split; [|split; [exact Rq | exact HP]]]]].
- exists Q. split; [|exact HO].
  apply (la_arep_zero _ (rdW W mem)); [exact HA | exact Hc | exact Ha | exact Hr | exact Hsp | | | exact Z16];
    intros a Ha'; apply K; lia.
- apply (la_aval_kept _ _ _ _ _ Hq). intros k Hk. apply K. right; right. lia.
Qed.

(* the listing's object atoms *)
Lemma la_ew_obj : forall E i v, img_env VAL A_LIM E -> (i < length cmd_objs)%nat -> nth i cmd_objs 0 = v ->
  (A_OBJ i < A_LIM)%nat -> ew E (A_OBJ i) = Z_to_bv 64 v.
Proof.
intros E i v HE Hi Hv Hl. pose proof (HE (A_OBJ i) ltac:(unfold A_OBJ, A_TEXT in *; lia)) as H.
rewrite (VOBJS i Hi), Hv in H. pose proof (pa_val_range (A_OBJ i)) as R. rewrite (VOBJS i Hi), Hv in R.
apply bv_eq. rewrite H. rewrite unsigned_lit_small by lia. reflexivity.
Qed.

(* the seed: the state at 0x8653c is an instance of ss_la *)
Lemma la_seed : forall (W : world SEGS) (regs : bvmap 5 word) mem,
  2 ^ 46 <= spZ regs -> spZ regs + 88 <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  (forall a, spZ regs <= a < spZ regs + 88 -> apresent (w_H W) mem a) ->
  getr regs 9 = w64 LT_SB ->
  aval_mem (rdW W mem) 0xa7068 8 A_G_REC -> aval_mem (rdW W mem) 0xa7070 8 LA_NC ->
  aval_mem (rdW W mem) 0xa7078 8 LT_CODES -> aval_mem (rdW W mem) LA_NC 4 LT_NCODES ->
  st_ok_pi SEGS VAL (la_E regs) ss_la
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_RC1RA)) mem (seg_rom SEGS))).
Proof.
intros W regs mem Hlo Hhi Hal Hpres R9 G2 G3 G4 GN.
set (E := la_E regs).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold la_E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs la_extra) n)
  by (intros n Hn; subst E; unfold la_E; apply Eimg_low; exact Hn).
assert (E2 : bv_unsigned (ew E 2) = spZ regs)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E9 : ew E 9 = Z_to_bv 64 LT_SB)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9).
assert (E32 : ew E 32 = Z_to_bv 64 LA_NC) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (EO2 : ew E (A_OBJ 2) = Z_to_bv 64 0xa7068)
  by (apply la_ew_obj; [exact HEI | vm_compute; lia | reflexivity | unfold A_OBJ, A_LIM; lia]).
assert (EO3 : ew E (A_OBJ 3) = Z_to_bv 64 0xa7070)
  by (apply la_ew_obj; [exact HEI | vm_compute; lia | reflexivity | unfold A_OBJ, A_LIM; lia]).
assert (EO4 : ew E (A_OBJ 4) = Z_to_bv 64 0xa7078)
  by (apply la_ew_obj; [exact HEI | vm_compute; lia | reflexivity | unfold A_OBJ, A_LIM; lia]).
assert (EO40 : ew E (A_OBJ 40) = Z_to_bv 64 LT_CODES)
  by (apply la_ew_obj; [exact HEI | vm_compute; lia | reflexivity | unfold A_OBJ, A_LIM; lia]).
assert (EO44 : ew E (A_OBJ 44) = Z_to_bv 64 A_G_REC)
  by (apply la_ew_obj; [exact HEI | vm_compute; lia | reflexivity | unfold A_OBJ, A_LIM; lia]).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
unfold ss_la. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- subst E. unfold la_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold la_regions, la_frame, la_ncodes, obj8_region.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite E2. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + rewrite (VB (A_OBJ 2) 0xa7068 EO2) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ 0xa7068 0 8 _ A_G_REC);
      [cbn [sv_denot]; rewrite EO44, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold A_G_REC; zside | zside |].
    rewrite Z.add_0_r. exact (la_val_of_aval SEGS _ mem _ 8 _ G2).
  + rewrite (VB (A_OBJ 3) 0xa7070 EO3) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ 0xa7070 0 8 _ LA_NC);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold LA_NC; zside | zside |].
    rewrite Z.add_0_r. exact (la_val_of_aval SEGS _ mem _ 8 _ G3).
  + rewrite (VB (A_OBJ 4) 0xa7078 EO4) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ 0xa7078 0 8 _ LT_CODES);
      [cbn [sv_denot]; rewrite EO40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold LT_CODES; zside | zside |].
    rewrite Z.add_0_r. exact (la_val_of_aval SEGS _ mem _ 8 _ G4).
  + rewrite (VB 32%nat LA_NC E32) by (unfold LA_NC; lia). unfold LA_NC. split; [lia|]. split; [lia|].
    split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ 0x21cc0 0 4 _ LT_NCODES); [reflexivity | unfold LT_NCODES; zside | zside |].
    rewrite Z.add_0_r. exact (la_val_of_aval SEGS _ mem _ 4 _ GN).
- apply pairwise_disjoint_of_extents. unfold la_regions, la_frame, la_ncodes, obj8_region, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB (A_OBJ 2) 0xa7068 EO2), (VB (A_OBJ 3) 0xa7070 EO3), (VB (A_OBJ 4) 0xa7078 EO4),
    (VB 32%nat LA_NC E32) by (unfold LA_NC; lia).
  cbn [base_val]. rewrite E2. unfold LA_NC.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  revert Hlo Hhi. clear. intros. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [la_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E2, E9, E32, EO40, EO44, !unsigned_lit_small by (unfold LT_SB, LA_NC, LT_CODES, A_G_REC; lia).
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  revert Hlo Hhi Hal. clear. intros.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia | reflexivity].
Qed.

(* the shadow entry of rec_ncodes holds at every state of AR *)
Lemma la_shok : forall ly S (W : world SEGS) mem md E, AR SEGS B ly S W mem md ->
  ew E 9 = Z_to_bv 64 LT_SB -> ew E 32 = Z_to_bv 64 LA_NC -> sh_ok SEGS LAx la_SH E (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md E HAR E9 E32. unfold sh_ok, la_SH. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) mem E LAx 32 LA_NC 4 LA_NC 0 4).
- apply (cmd_addressable_chk SEGS B LAWS HB ly S W mem md _ _ HAR). vm_compute. reflexivity.
- unfold U, LAx. cbn [sv_denot]. rewrite E9, Z.add_0_r, Z_to_bv_bv_unsigned.
  rewrite unsigned_lit_small by (unfold LT_SB; lia). reflexivity.
- unfold U. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
  rewrite unsigned_lit_small by (unfold LA_NC; lia). reflexivity.
- lia.
- lia.
- intros x Hx. unfold LA_NC, SHADOW_OFF in *. cbn in Hx. lia.
Qed.

End e.
End f.
End d.
