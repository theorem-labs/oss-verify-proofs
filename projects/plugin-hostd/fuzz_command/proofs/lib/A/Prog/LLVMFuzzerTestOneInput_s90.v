(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: segment Z2 of LLVMFuzzerTestOneInput's ASan walk (plugin-hostd/fuzz_command, 0x86a10 .. ret 0x86a68: g_quitting = 0 through its inline check, a0 = 0, the 13 restores, the return), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (cl_seedX: the seed of a state inside the function, its saved registers as frame chunks) and A/ACbk.v (the return into the function's post). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m ACfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaSB PaLibF.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdAddr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_clear_c send_message_c check_reply_c check_arity_c check_words_c check_refusal_c check_round_trip_c
verbs_receive_c LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s01.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the seed state at 0x86a10 (LO_RC2RA) ----
   The environment's atoms 0 .. 31 are the ENTRY's registers (x_regs), so the frame chunks of the saved registers
   are the atoms of those registers and the restores leave every callee-saved register as its own atom (the
   return's aregs_preserved by aregs_preserved_of_st_ok). Atom 32 is the shadow base (s1), 33 g_quitting's
   address, 34 + i the value register i holds at 0x86a10. The symbolic registers: sp = entry sp - 256, gp and tp the
   entry's, s1 = atom 32, every other one its own atom 34 + i. Regions: the 13 saved words at entry sp - 8 ..
   entry sp - 104, g_quitting's GOT word (listing object 6, 0xa7080), g_quitting's 4 bytes (written, no chunk). *)
Definition lz_sreg (i : nat) : sv :=
match i with O => SLit 0 | 2%nat => SOff 2 (-256) | 3%nat => SOff 3 0 | 4%nat => SOff 4 0 | 9%nat => SOff 32 0
| _ => SOff (34 + i)%nat 0 end.
Definition lz_sregs : list sv := map lz_sreg (seq 0 32).
Definition lz_frame : YP09.region :=
YP09.mkRegion (Some 2%nat) (-104) 0 0 0
[YP09.mkChunk (-8) (CVal 8 (SOff 1 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0));
 YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0));
 YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0)); YP09.mkChunk (-72) (CVal 8 (SOff 23 0));
 YP09.mkChunk (-80) (CVal 8 (SOff 24 0)); YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0));
 YP09.mkChunk (-104) (CVal 8 (SOff 27 0))].
Definition lz_quit : YP09.region := YP09.mkRegion (Some 33%nat) 0 4 0 4 [].
Definition lz_regions : smem := [lz_frame; obj8_region 6 (SOff 33 0); lz_quit].
Definition lz_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF LT_SB LT_SB 0); (33%nat, mkAF A_G_QUITTING A_G_QUITTING 5) ] [] [].
Definition lz_SH : list shent := [mkSHE 33 0 4].
Definition LZx : sv := SOff 32 0.
Definition LZspan : Z * Z := (LT_SB, LT_SB + 2 ^ 44 - 1).
Definition ss_lz : sstate := mkSS LO_RC2RA lz_sregs lz_regions None lz_facts.

(* ---- readers: fields kept, zero fields ---- *)
Lemma lz_aval_kept : forall (rd rd' : reader) a n v,
  (forall k, (k < n)%nat -> rd' (a + Z.of_nat k) = rd (a + Z.of_nat k)) -> aval_mem rd a n v -> aval_mem rd' a n v.
Proof. intros rd rd' a n v HK H k Hk. rewrite (HK k Hk). exact (H k Hk). Qed.
Lemma lz_zero_aval : forall (rd : reader) a (n : nat), aval_mem rd a n 0 -> zero_atA rd a (Z.of_nat n).
Proof.
intros rd a n H i Hi. pose proof (H (Z.to_nat i) ltac:(lia)) as Hk. rewrite Z2Nat.id in Hk by lia. rewrite Hk.
f_equal. unfold YG0f.le_byte. rewrite Zmod_0_l, Z.shiftr_0_l. reflexivity.
Qed.
Lemma lz_zero_cat : forall (rd : reader) a n1 n2,
  zero_atA rd a n1 -> zero_atA rd (a + n1) n2 -> 0 <= n1 -> zero_atA rd a (n1 + n2).
Proof.
intros rd a n1 n2 H1 H2 Hn i Hi. destruct (Z_lt_le_dec i n1) as [Hl|Hl]; [apply H1; lia|].
replace (a + i) with (a + n1 + (i - n1)) by lia. apply H2. lia.
Qed.
Ltac lz_rng := unfold A_G_REC, A_REC_SPILL, A_G_QUITTING, OFF_NCALLS, OFF_ANSWER, OFF_NREPLIES, OFF_REPLY,
  OFF_REPLY_SIZE, OFF_STATE, OFF_HOST, OFF_REFUSE, OFF_CODE, CALL_OFF_FN, CALL_OFF_NARGS; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
(* the recorder after rec_clear, with no spilled call, reads only g_rec and record.spill: both lie below g_quitting *)
Lemma lz_arep_kept : forall bl (rd rd' : reader) R Q,
  (forall a, 0 <= a < A_G_QUITTING -> rd' a = rd a) -> r_spill R = (0, []) ->
  arep_at bl rd A_G_REC A_REC_SPILL (RecModel.rec_clear R) Q ->
  arep_at bl rd' A_G_REC A_REC_SPILL (RecModel.rec_clear R) Q.
Proof.
intros bl rd rd' R Q HK Hsp (H1 & H2 & H3 & (C1 & C2 & C3 & C4 & C5 & C6) & HA & HR & (S1 & S2 & S3 & S4 & S5 & S6) & HO).
assert (K : forall a (n : nat) v, 0 <= a -> a + Z.of_nat n <= A_G_QUITTING -> aval_mem rd a n v -> aval_mem rd' a n v).
{ intros a n v Ha Hn Hv. apply (lz_aval_kept rd); [|exact Hv]. intros j Hj. apply HK. lia. }
cbn [RecModel.rec_clear r_calls r_spill r_answer r_reply r_nreplies r_refuse r_code r_state r_host] in *.
rewrite Hsp in C5, C6.
unfold arep_at, ag1_calls, ag1_scalars. cbn [RecModel.rec_clear r_calls r_spill r_answer r_reply r_nreplies r_refuse r_code r_state r_host].
rewrite Hsp.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
split.
{ split; [exact C1|]. split; [exact C2|]. split; [apply K; [lz_rng | lz_rng | exact C3]|].
  split; [intros i c P Hi; destruct i; discriminate Hi|].
  split; [|exact C6].
  destruct C5 as (A1 & A2 & A3 & A4 & A5 & A6 & A7).
  split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
  split; [apply K; [lz_rng | lz_rng | exact A4]|]. split; [apply K; [lz_rng | lz_rng | exact A5]|].
  split; [exact A6|]. intros k s pn Hk. destruct k; discriminate Hk. }
split.
{ unfold aanswer_at in *. destruct (l_answer Q); [destruct HA|]. apply K; [lz_rng | lz_rng | exact HA]. }
split.
{ unfold areply_at in *. destruct (l_reply Q); [destruct HR|]. destruct HR as [HR1 HR2].
  split; (apply K; [lz_rng | lz_rng |]); assumption. }
split; [|exact HO].
split; [apply K; [lz_rng | lz_rng | exact S1]|]. split; [apply K; [lz_rng | lz_rng | exact S2]|].
split; [apply K; [lz_rng | lz_rng | exact S3]|]. split; [apply K; [lz_rng | lz_rng | exact S4]|].
split; [apply K; [lz_rng | lz_rng | exact S5] | exact S6].
Qed.
(* the global invariant at the return: rec_clear's recorder with no spilled call, and g_quitting = 0 *)
Lemma lz_gi : forall bl (rd : reader) R Q j,
  arep_at bl rd A_G_REC A_REC_SPILL (RecModel.rec_clear R) Q -> r_spill R = (0, []) ->
  aval_mem rd A_G_QUITTING 4 0 -> GI_cmdA j rd.
Proof.
intros bl rd R Q j (_ & _ & _ & (_ & _ & C3 & _ & C5 & _) & HA & HR & (_ & _ & S3 & _) & _) Hsp HQ.
cbn [RecModel.rec_clear r_calls r_spill r_answer r_reply r_nreplies length Z.of_nat] in *.
rewrite Hsp in C5. destruct C5 as (_ & _ & _ & A4 & A5 & _). cbn [fst snd length Z.of_nat] in A4, A5.
unfold aanswer_at in HA. destruct (l_answer Q); [destruct HA|].
unfold areply_at in HR. destruct (l_reply Q); [destruct HR|]. destruct HR as [HR1 HR2].
unfold OFF_NCALLS, OFF_ANSWER, OFF_NREPLIES, OFF_REPLY, OFF_REPLY_SIZE, CALL_OFF_FN, CALL_OFF_NARGS in *.
rewrite Z.add_0_r in A4.
unfold GI_cmdA.
split; [exact (lz_zero_aval _ _ 4 C3)|].
split.
{ change 12 with (8 + 4). apply lz_zero_cat; [exact (lz_zero_aval _ _ 8 HA) | | lia].
  replace (A_G_REC + 912 + 8) with (A_G_REC + 920) by lia. exact (lz_zero_aval _ _ 4 S3). }
split.
{ change 16 with (8 + 8). apply lz_zero_cat; [exact (lz_zero_aval _ _ 8 HR1) | | lia].
  replace (A_G_REC + 928 + 8) with (A_G_REC + 936) by lia. exact (lz_zero_aval _ _ 8 HR2). }
split.
{ change 8 with (4 + 4). apply lz_zero_cat; [exact (lz_zero_aval _ _ 4 A4) | exact (lz_zero_aval _ _ 4 A5) | lia]. }
exact (lz_zero_aval _ _ 4 HQ).
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Definition lz_extra (regs : bvmap 5 word) : list word :=
  Z_to_bv 64 LT_SB :: Z_to_bv 64 A_G_QUITTING :: map (fun i => getr regs (Z_to_bv 5 (Z.of_nat i))) (seq 0 32).
Definition lz_E (xr regs : bvmap 5 word) : env := Eimg (Ereg xr (lz_extra regs)).

Lemma lz_ew_hi : forall xr regs n, (34 <= n < 66)%nat ->
  ew (lz_E xr regs) n = getr regs (Z_to_bv 5 (Z.of_nat (n - 34))).
Proof.
intros xr regs n Hn. unfold lz_E. rewrite Eimg_low by (unfold A_TEXT; lia).
replace n with (32 + S (S (n - 34)))%nat at 1 by lia. rewrite ew_Ereg_extra. unfold lz_extra. cbn [nth].
set (g := fun i : nat => getr regs (Z_to_bv 5 (Z.of_nat i))).
rewrite nth_indep with (d' := g 0%nat) by (rewrite length_map, length_seq; lia).
rewrite map_nth, seq_nth by lia. unfold g. reflexivity.
Qed.
Lemma lz_ew_lo : forall xr regs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (lz_E xr regs) n = getr xr r.
Proof.
intros xr regs n r Hr. pose proof (u5_range r) as R5. unfold lz_E. rewrite Eimg_low by (unfold A_TEXT; lia).
apply ew_Ereg_nat. exact Hr.
Qed.
Lemma lz_ew32 : forall xr regs, ew (lz_E xr regs) 32 = Z_to_bv 64 LT_SB.
Proof. intros xr regs. unfold lz_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra xr (lz_extra regs) 0). Qed.
Lemma lz_ew33 : forall xr regs, ew (lz_E xr regs) 33 = Z_to_bv 64 A_G_QUITTING.
Proof. intros xr regs. unfold lz_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra xr (lz_extra regs) 1). Qed.

Lemma lz_regs_ok : forall xr regs,
  getr regs 2 = Z_to_bv 64 (bv_unsigned (getr xr 2) + -256) -> getr regs 3 = getr xr 3 -> getr regs 4 = getr xr 4 ->
  getr regs 9 = Z_to_bv 64 LT_SB -> regs_ok (lz_E xr regs) lz_sregs regs.
Proof.
intros xr regs R2 R3 R4 R9.
apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr];
  [ match goal with |- _ = sv_denot ?E (sr_get ?sr ?r) =>
      let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
    cbn [sv_denot];
    first
    [ rewrite getr_zero; reflexivity
    | rewrite lz_ew32, Z.add_0_r, Z_to_bv_bv_unsigned; exact R9
    | rewrite (lz_ew_lo xr regs 2%nat 2%bv) by reflexivity; exact R2
    | rewrite (lz_ew_lo xr regs 3%nat 3%bv) by reflexivity; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact R3
    | rewrite (lz_ew_lo xr regs 4%nat 4%bv) by reflexivity; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact R4
    | rewrite lz_ew_hi by lia; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; f_equal; apply bv_eq; vm_compute; reflexivity ]
  | ]).
destruct Hr.
Qed.

(* the listing's object i is at the address the record names (cmd_val_objs) *)
Lemma lz_ew_obj : cmd_val_objs -> forall E i v, img_env VAL A_LIM E -> (i < length cmd_objs)%nat ->
  nth i cmd_objs 0 = v -> (A_OBJ i < A_LIM)%nat -> ew E (A_OBJ i) = Z_to_bv 64 v.
Proof.
intros VOBJS E i v HE Hi Hv Hl. pose proof (HE (A_OBJ i) ltac:(unfold A_OBJ, A_TEXT in *; lia)) as H.
rewrite (VOBJS i Hi), Hv in H. pose proof (pa_val_range (A_OBJ i)) as R. rewrite (VOBJS i Hi), Hv in R.
apply bv_eq. rewrite H. rewrite unsigned_lit_small by lia. reflexivity.
Qed.
Lemma lz_val_of_aval : forall H (mem : word -> option byte) a n v,
  aval_mem (aview SEGS H mem) a n v -> val_mem SEGS (mrestrict H mem) a n v.
Proof.
intros H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte SEGS (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Eb; cbn in Hv; [|discriminate Hv].
injection Hv as Hb. rewrite <- (Z_to_bv_bv_unsigned 8 b). rewrite Hb. reflexivity.
Qed.
Lemma lz_aval_of_val : forall H (mem : word -> option byte) a n v,
  val_mem SEGS (mrestrict H mem) a n v -> aval_mem (aview SEGS H mem) a n v.
Proof.
intros H mem a n v Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
unfold YO0f.le_byte, YG0f.le_byte. apply Z.mod_mod. lia.
Qed.
(* g_quitting's GOT word from cmd_ro_ok's bytes (CmdRo.v RO_ptr_a7080) *)
Lemma lz_got_of_ro : forall rd, cmd_ro_ok rd -> aval_mem rd 0xa7080 8 A_G_QUITTING.
Proof.
intros rd [HRO _]. unfold cmd_ro_bytes in HRO.
assert (H2 : abytes_atR rd 0xa7080 RO_ptr_a7080).
{ clear - HRO. repeat match type of HRO with
  | abytes_atR _ 0xa7080 _ /\ _ => exact (proj1 HRO)
  | abytes_atR _ 0xa7080 _ => exact HRO
  | _ /\ _ => apply proj2 in HRO end. }
intros k Hk. rewrite (H2 k) by (cbn [length RO_ptr_a7080]; exact Hk). f_equal.
do 8 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
Qed.
(* one saved register's word in the frame *)
Lemma lz_chunk : forall (E : env) mem (W : world SEGS) cx (n : nat) (r : bv 5) (j : nat),
  ew E n = getr (x_regs cx) r -> nth_error LT_SAVED j = Some r -> lt_saved cx (rdW W mem) ->
  YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) (x_sp0 cx) (YP09.mkChunk (-8 * Z.of_nat (S j)) (CVal 8 (SOff n 0))).
Proof.
intros E mem W cx n r j Hn Hj HSV.
apply (chunk_ok_val SEGS E _ _ _ 8%N _ (bv_unsigned (getr (x_regs cx) r))).
- cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- pose proof (bv_unsigned_in_range 64 (getr (x_regs cx) r)) as HR. change (bv_modulus 64) with (2 ^ 64) in HR. exact HR.
- cbn. lia.
- replace (x_sp0 cx + -8 * Z.of_nat (S j)) with (x_sp0 cx - 8 * Z.of_nat (S j)) by lia.
  exact (val_mem_of_rdword SEGS _ _ _ _ (HSV j r Hj)).
Qed.
(* a chunk of a region of a symbolic memory that holds *)
Lemma lz_chunk_of : forall E m (rs : smem) r c, YP09.mem_ok SEGS E m rs -> In r rs -> In c (YP09.r_chunks r) ->
  YP09.chunk_ok SEGS E m (base_val E (YP09.r_base r)) c.
Proof. intros E m rs r c HM Hr Hc. eapply region_ok_chunk; [eapply mem_ok_region; [exact HM | exact Hr] | exact Hc]. Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* the walk's Section hypotheses, with cgif's names *)
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis PRW : prog_rw SEGS B.
(* the record's facts are the lemmas of lib/A/Prog/CmdRecBase.v (cmd_addressable_chk), CmdRecCells.v
   (PROG_WRITABLE) and CmdRecImg.v (cmd_prog_unowned); the image facts IMG close at assembly by cmd_img_facts_tfib,
   and the read-only range is in the image by its field cif_relro_img *)
Hypothesis IMG : cmd_img_facts SEGS B.
Let RRO : forall a, CMD_RLO <= a < CMD_RHI -> in_img SEGS a := cif_relro_img SEGS B IMG.
Let RUN := paj_run B LAWS.
Let RET := paj_ret_at (PL := PL_cmd) (PI := PI).

Lemma lz_PG_quit : forall a, A_G_QUITTING <= a < A_G_QUITTING + 4 -> inFP cmd_PG a.
Proof. intros a Ha. exists (A_G_QUITTING, A_G_QUITTING + 4). split; [right; right; left; reflexivity | cbn [fst snd]; lia]. Qed.
Lemma lz_prog_quit : forall a, A_G_QUITTING <= a < A_G_QUITTING + 4 -> Exists (in_zr a) (as_prog_static B).
Proof.
intros a Ha. rewrite (ts_prog B HB). unfold TFIB_PROG_STATIC.
apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd. unfold in_zr. cbn [fst snd]. unfold A_G_QUITTING in Ha. lia.
Qed.
(* the GOT word 0xa7080 is an image byte of the read-only range, outside the runtime-owned statics, the errno cell
   and the footprint: every journal from the entry keeps it *)
Lemma lz_got_kept : forall a, 0xa7080 <= a < 0xa7088 ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4) /\ fp_spares cmd_PG a.
Proof.
intros a Ha. split; [apply RRO; unfold CMD_RLO, CMD_RHI; lia|]. split; [|split].
- rewrite (ts_owned B HB). intros HE. apply Exists_exists in HE as ([lo n] & Hin & Hz). unfold in_zr in Hz. cbn [fst snd] in Hz.
  assert (HF : forallb (fun r => (fst r + snd r <=? 0xa7080) || (0xa7088 <=? fst r)) Tfib_owned_static = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in HF. specialize (HF _ Hin). cbn [fst snd] in HF.
  apply orb_true_iff in HF as [HF|HF]; apply Z.leb_le in HF; lia.
- rewrite (ts_errno B HB). unfold TFIB_ERRNO. lia.
- apply fp_spares_closed.
  + apply sink_closed_pos. unfold cmd_PG, A_G_REC, A_REC_SPILL, A_G_QUITTING.
    repeat constructor; cbn [fst]; lia.
  + intros (r & Hr & Hlo & Hhi). unfold cmd_PG in Hr. cbn [In] in Hr.
    destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hlo, Hhi; unfold A_G_REC, A_REC_SPILL, A_G_QUITTING in *; lia.
Qed.
Lemma lz_got_loc : forall cx ly S (W : world SEGS) mem md k,
  lt_base B MT cx ->
  ajournal SEGS B LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [] ly S W mem md k ->
  aval_mem (rdW W mem) 0xa7080 8 A_G_QUITTING.
Proof.
intros cx ly S W mem md k HB0 HJ.
pose proof HB0 as (_ & _ & HRO & _).
pose proof (lz_got_of_ro _ HRO) as G6.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
intros j Hj. destruct (lz_got_kept (0xa7080 + Z.of_nat j) ltac:(lia)) as (K1 & K2 & K3 & K4).
rewrite (F3 _ K1 K2 K3 K4). exact (G6 j Hj).
Qed.

(* the seed: the symbolic state at 0x86a10 and the shadow entry of g_quitting *)
Lemma lz_seed : forall cx (W : world SEGS) regs mem,
  lt_base B MT cx -> spZ regs = x_sp1 cx -> getr regs 3 = getr (x_regs cx) 3 -> getr regs 4 = getr (x_regs cx) 4 ->
  getr regs 9 = w64 LT_SB -> lt_saved cx (rdW W mem) ->
  aval_mem (rdW W mem) 0xa7080 8 A_G_QUITTING ->
  range_addressable (rdW W mem) SHADOW_OFF A_G_QUITTING 4 ->
  st_ok_pi SEGS VAL (lz_E (x_regs cx) regs) ss_lz
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_RC2RA)) mem (seg_rom SEGS)))
  /\ sh_ok SEGS LZx lz_SH (lz_E (x_regs cx) regs) (mrestrict (w_H W) mem).
Proof.
intros cx W regs mem HB0 Hsp R3 R4 R9 HSV G6 ZQ.
pose proof HB0 as (HPRE & _ & _ & HOBJ & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hs0 : 0x7fff7f800000 <= x_sp0 cx <= 2 ^ 47) by (unfold x_sp0; lia).
assert (R2 : getr regs 2 = Z_to_bv 64 (bv_unsigned (getr (x_regs cx) 2) + -256)).
{ apply bv_eq. rewrite unsigned_lit_small by (unfold x_sp0, spZ in Hs0; lia).
  unfold x_sp1, x_sp0, LT_FRAME, spZ in Hsp. lia. }
set (E := lz_E (x_regs cx) regs).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold lz_E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr (x_regs cx) r)
  by (intros n r Hr; subst E; exact (lz_ew_lo _ _ n r Hr)).
assert (E32 : ew E 32 = Z_to_bv 64 LT_SB) by (subst E; apply lz_ew32).
assert (E33 : ew E 33 = Z_to_bv 64 A_G_QUITTING) by (subst E; apply lz_ew33).
assert (EO6 : ew E (A_OBJ 6) = Z_to_bv 64 0xa7080)
  by (apply (lz_ew_obj HOBJ); [exact HEI | vm_compute; lia | reflexivity | unfold A_OBJ, A_LIM; lia]).
assert (Usp0 : bv_unsigned (ew E 2) = x_sp0 cx) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
split.
- unfold ss_lz. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + subst E. apply lz_regs_ok; [exact R2 | exact R3 | exact R4 | exact R9].
  + vm_compute. reflexivity.
  + unfold lz_regions, lz_frame, obj8_region, lz_quit.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp0. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [exact (lz_chunk E mem W cx 1%nat 1%bv 0%nat (EE 1%nat 1%bv eq_refl) eq_refl HSV)|].
      constructor; [exact (lz_chunk E mem W cx 8%nat 8%bv 1%nat (EE 8%nat 8%bv eq_refl) eq_refl HSV)|].
      constructor; [exact (lz_chunk E mem W cx 9%nat 9%bv 2%nat (EE 9%nat 9%bv eq_refl) eq_refl HSV)|].
      constructor; [exact (lz_chunk E mem W cx 18%nat 18%bv 3%nat (EE 18%nat 18%bv eq_refl) eq_refl HSV)|].
      constructor; [exact (lz_chunk E mem W cx 19%nat 19%bv 4%nat (EE 19%nat 19%bv eq_refl) eq_refl HSV)|].
      constructor; [exact (lz_chunk E mem W cx 20%nat 20%bv 5%nat (EE 20%nat 20%bv eq_refl) eq_refl HSV)|].
      constructor; [exact (lz_chunk E mem W cx 21%nat 21%bv 6%nat (EE 21%nat 21%bv eq_refl) eq_refl HSV)|].
      constructor; [exact (lz_chunk E mem W cx 22%nat 22%bv 7%nat (EE 22%nat 22%bv eq_refl) eq_refl HSV)|].
      constructor; [exact (lz_chunk E mem W cx 23%nat 23%bv 8%nat (EE 23%nat 23%bv eq_refl) eq_refl HSV)|].
      constructor; [exact (lz_chunk E mem W cx 24%nat 24%bv 9%nat (EE 24%nat 24%bv eq_refl) eq_refl HSV)|].
      constructor; [exact (lz_chunk E mem W cx 25%nat 25%bv 10%nat (EE 25%nat 25%bv eq_refl) eq_refl HSV)|].
      constructor; [exact (lz_chunk E mem W cx 26%nat 26%bv 11%nat (EE 26%nat 26%bv eq_refl) eq_refl HSV)|].
      constructor; [exact (lz_chunk E mem W cx 27%nat 27%bv 12%nat (EE 27%nat 27%bv eq_refl) eq_refl HSV)|].
      constructor.
    * rewrite (VB (A_OBJ 6) 0xa7080 EO6) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ 0xa7080 0 8%N _ A_G_QUITTING);
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold A_G_QUITTING; zside | zside |].
      rewrite Z.add_0_r. exact (lz_val_of_aval _ mem _ 8 _ G6).
    * rewrite (VB 33%nat A_G_QUITTING E33) by (unfold A_G_QUITTING; lia). split; [unfold A_G_QUITTING; lia|].
      split; [unfold A_G_QUITTING; lia|]. split; [|constructor].
      intros o Ho. apply (PROG_WRITABLE SEGS B LAWS HB PRW). apply lz_PG_quit. lia.
  + apply pairwise_disjoint_of_extents. unfold lz_regions, lz_frame, obj8_region, lz_quit, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 6) 0xa7080 EO6), (VB 33%nat A_G_QUITTING E33) by (unfold A_G_QUITTING; lia).
    cbn [base_val]. rewrite Usp0. unfold A_G_QUITTING.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hs0. clear. intros. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [lz_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp0, E32, E33, !unsigned_lit_small by (unfold LT_SB, A_G_QUITTING; lia).
    unfold LT_SB, A_G_QUITTING. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold x_sp0 in Hs0 |- *.
    revert Hs0 Hal16. clear. intros.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia | reflexivity].
- unfold sh_ok, lz_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) mem E LZx 33 A_G_QUITTING 4 A_G_QUITTING 0 4 ZQ).
  + unfold U, LZx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by (unfold LT_SB; lia). reflexivity.
  + unfold U. cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by (unfold A_G_QUITTING; lia). reflexivity.
  + lia.
  + lia.
  + intros x Hx. unfold A_G_QUITTING, SHADOW_OFF in *. cbn in Hx. lia.
Qed.

(* ---- segment Z2: 0x86a10 .. ret 0x86a68 ---- *)
Lemma lt_seg_Z2 : LT_Z2_stmt B MT.
Proof.
unfold LT_Z2_stmt.
intros cx ly S W regs mem md k acc R q HB0 Hfrm HFR R9 HREC HBUD.
pose proof pa_segs_low as Hsegs. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HFR as (HJ & Hsp & R3 & R4 & HSV).
pose proof HB0 as (HPRE & _ & _ & HOBJ & _ & _ & Hpn & _).
pose proof HPRE as (_ & Hra & _).
pose proof HREC as (HRR & Hspill & Hcalls2 & _ & _ & HPERM).
pose proof HBUD as (Hk0 & _ & Hkrem & Hmle & Hacc0 & Hacc).
cbn [app] in HPERM. rewrite app_nil_r in HPERM. unfold x_bl0 in HPERM.
pose proof (proj1 HJ) as HAR.
pose proof (cmd_addressable_chk SEGS B LAWS HB ly S W mem md A_G_QUITTING 4 HAR ltac:(vm_compute; reflexivity)) as ZQ.
pose proof (lz_got_loc cx ly S W mem md k HB0 HJ) as G6.
destruct (lz_seed cx W regs mem HB0 Hsp R3 R4 R9 HSV G6 ZQ) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (lz_E (x_regs cx) regs)) by (unfold lz_E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg (x_regs cx) (lz_extra regs)) (lz_E (x_regs cx) regs)).
{ split; [intros n Hn; unfold lz_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]. }
assert (E33u : bv_unsigned (ew (lz_E (x_regs cx) regs) 33) = A_G_QUITTING)
  by (rewrite lz_ew33; apply unsigned_lit_small; unfold A_G_QUITTING; lia).
assert (E1 : ew (lz_E (x_regs cx) regs) 1 = getr (x_regs cx) 1) by (apply lz_ew_lo; reflexivity).
remember (lz_E (x_regs cx) regs) as E eqn:HE. clear HE.
(* 0x86a10 .. 0x86a68: g_quitting's address through its GOT word, its check through the slow block (the shadow
   entry covers its 4 bytes), g_quitting = 0, a0 = 0, the 13 restores, sp += 256 *)
paj_run_tok RUN HS HJ SHOK LZspan.
{ lazymatch goal with |- awr_ok ?sg ?bb ?E0 ?rs ?stk ?sp0 ?fp ?b0 ?bc ?fr ?ly0 ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb E0 rs' stk sp0 fp b0 bc fr ly0 own) end.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen; [reflexivity | exact E33u | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
  right; right; right; right. left.
  split; [exact (lz_PG_quit a ltac:(lia))|].
  split; [exact (lz_prog_quit a ltac:(lia)) | exact (proj1 (cmd_prog_unowned SEGS B LAWS HB IMG a (lz_PG_quit a ltac:(lia))))]. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
(* memory outside g_quitting's 4 bytes is kept by the run *)
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (A_G_QUITTING <= a < A_G_QUITTING + 4) ->
  rdW W (ms_mem ms) a = rdW W mem a).
{ intros a Ha Hn.
  apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => A_G_QUITTING <= a < A_G_QUITTING + 4) HFr); [|exact Ha | exact Hn].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  repeat (destruct Hin as [Hq0 | Hin]; [injection Hq0 as <- <- <-; cbn [base_val] in Hrr; rewrite ?E33u in Hrr; lia|]).
  destruct Hin. }
(* g_quitting holds 0 *)
assert (HQ0 : aval_mem (rdW W (ms_mem ms)) A_G_QUITTING 4 0).
{ pose proof (st_ok_mem_ok SEGS _ _ _ HS) as HM. cbn [abs_ss setpc ss_mem restrict ms_mem] in HM.
  pose proof (lz_chunk_of _ _ _ _ _ HM (in_cons _ _ _ (in_cons _ _ _ (in_eq _ _))) (in_eq _ _)) as HC.
  cbn [YP09.r_base YP09.r_chunks base_val ew ewset Nat.eqb] in HC. rewrite E33u in HC.
  pose proof (val_of_chunk_ok SEGS _ _ _ 0 4%N (SLit 0) 0 HC eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as HV.
  rewrite Z.add_0_r in HV. exact (lz_aval_of_val _ _ _ 4 0 HV). }
prreg HS (1%bv : bv 5) F1.
prreg HS (10%bv : bv 5) F10.
assert (HAE2 : forall E4, (forall n, (n < 32)%nat -> ew E4 n = ew E n) -> ed E4 = ed E ->
  env_agree 32 (Ereg (x_regs cx) (lz_extra regs)) E4).
{ intros E4 H1 H2. destruct HAE as [HA1 HA2]. split; [intros n Hn; rewrite H1 by exact Hn; exact (HA1 n Hn) | rewrite H2; exact HA2]. }
lazymatch type of HS with st_ok_pi _ _ ?E4 _ _ =>
  assert (HAE4 : env_agree 32 (Ereg (x_regs cx) (lz_extra regs)) E4) end.
{ apply HAE2; [intros n Hn; cbn [ew ewset];
    repeat match goal with |- context [Nat.eqb ?a ?b] => destruct (Nat.eqb_spec a b); [lia|] end; reflexivity
  | cbn [ed ewset]; reflexivity]. }
pose proof (aregs_preserved_of_st_ok SEGS _ _ _ _ (x_regs cx) (lz_extra regs) HS HAE4 ltac:(vm_compute; reflexivity)) as HPRS.
assert (HPERM' : Permutation (ablocks B ly S) (ablocks B (x_ly cx) (x_S cx))) by exact HPERM.
assert (HIN : 0 < x_n cx -> In (x_p cx, x_n cx) (ablocks B ly S)).
{ intros Hn. destruct Hpn as [[Hn0 _] | [_ Hin0]]; [lia|].
  exact (Permutation_in _ (Permutation_sym HPERM') Hin0). }
assert (HKr : forall a, 0 <= a < A_G_QUITTING -> rdW W (ms_mem ms) a = rdW W mem a)
  by (intros a Ha; apply KEEP; unfold A_G_QUITTING in *; lia).
destruct HRR as (Q & HAQ & HOQ).
pose proof (lz_arep_kept _ _ _ R Q HKr Hspill HAQ) as HAQ'.
assert (HLV : 0 <= LIVE_LTOI) by (apply Z.leb_le; vm_compute; reflexivity).
(* the return *)
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold lt_post, apost_baseF.
exists fx.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly, S, r, m, d end.
split; [rewrite F1, E1; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
(* the walk does not touch the FP state: the FP registers and the csr are the entry's *)
split; [intros k0 _; reflexivity|].
split; [left; reflexivity|].
split; [eapply ajournal_mono_k; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ | lia]|].
split; [exact HPRS|].
unfold lt_Q.
split; [unfold w64; exact F10|].
split; [exact HPERM'|].
split; [exact (lt_payload_kept B MT cx ly S W (ms_mem ms) mdv [] k HB0 HJ HIN)|].
split.
{ exists R. unfold cmd_rec_invA.
  split; [exists Q; split; [exact HAQ' | exact HOQ]|].
  split; [exact Hspill|]. split; [exact Hcalls2|]. split; [exact HQ0|]. split; [lia|].
  cbn [app]. exact HPERM'. }
split; [exact (lz_gi _ _ R Q _ HAQ' Hspill HQ0)|].
split; [apply (mo_le_mono MT MTL _ _ _ _ Hmle); rewrite Z.mul_0_l, Z.add_0_r in Hacc; exact Hacc|].
rewrite (blocks_bytes_ablocks B ly S), (blocks_bytes_ablocks B (x_ly cx) (x_S cx)), (bsum_perm _ _ HPERM'). lia.
Qed.

End e.
End f.
End d.
