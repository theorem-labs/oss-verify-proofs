(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the helpers of sup_after_reply's ASan+UBSan walk (plugin-hostd/fuzz_command,
   fuzz_command.asan-ubsan, entry 0x8c758, 120 instructions, lib/B/Prog/sup_after_reply.v): the format "%d" of the
   arg_i code B inlines (.str 0x21f40, the listing's object A_OBJ 51) with its bytes, shadow and fmt_at form, and the
   decimal text snprintf(b, 16, "%d", id) writes as the recorder's string; the frame's realignment `andi sp,sp,-32`
   (0x8c790) on a Theorem Labs lane's CmdSnText helpers; the symbolic entry state with its seed; the words and bytes a region of
   the symbolic state records; the frame chain at a call whose s0 is the frame pointer (achain_push); the recorder's
   state across writes outside it; the model step.
   TAKEN FROM: the ASan walk of answer_code (lib/A/Prog/answer_code.v, a working branch 2ba4488ce71, lines
   28-527: the region helpers, rec_repA_kept and its parts, the entry seed with the realigned sp as an atom) and the
   ASan walk of arg_i (lib/A/Prog/arg_i_s0.v, a working branch 12dc52bfe84: the "%d" facts). B inlines arg_i
   into sup_after_reply; the frame code (0x8c758-0x8c854, 0x8c8a0-0x8c934) is arg_i's (A 0x8a238-0x8a32c,
   0x8a3b0-0x8a444) with the registers renamed. The literal's shadow comes from the allocator record (lib/B/YF0m.v),
   as in lib/B/Prog/sup_lv2_worker_set_aux.v (a working branch 5c04ebe0308). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI09 YG0s YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v YI0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC5d YM05 YG05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0d_tail.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YN0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
CmdSyms CmdList CmdAddr CmdPa CmdPaLib PaLibG PaDenot PaLibF PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaSB PaCallRun PaCall.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtPFShared RtPFCmd.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import record_c RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdSnText.
(* the plain proof's printf facts on "%d" (lib/Prog/arg_i.v:36-54); B has no arg_i walk, so the module is named by its
   full path as the ASan walk names it *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require arg_i.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Module PAI := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.arg_i.

(* ---------- tactics (the ASan answer_code walk's preg / norm_ssp / nwin_tac) ---------- *)
(* a register's symbolic value in a symbolic state, its denotation not normalised *)
Ltac sar_preg HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
cbn [ms_regs restrict mkst] in Hr
| st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
cbn [ms_regs restrict mkst] in Hr
end.
Ltac sar_norm HS :=
lazymatch type of HS with
| st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS
| st_ok _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS
end.
(* an address outside every write window of a symbolic memory *)
Ltac sar_nwin rwt :=
let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros (r & Hin & Hr);
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rwt Hr | ]);
destruct Hin.
(* the conjunct of a long conjunction that holds the literal address [a]: drop the leading conjuncts of H in place *)
Ltac sar_projz H a :=
  repeat lazymatch type of H with
  | ?A /\ _ => lazymatch A with context [a] => fail | _ => destruct H as [_ H] end
  end;
  lazymatch type of H with
  | _ /\ _ => exact (proj1 H)
  | _ => exact H
  end.

(* ---------- the format "%d" and the text it gives ---------- *)
(* "%d" and its terminator are the read-only literal at 0x21f40 (B's CmdRo.v RO_lit_21f40) *)
Lemma sar_fmt_bytes : PF.pf_bytes PAI.AI_FMT ++ [Z_to_bv 8 0] = RO_lit_21f40.
Proof. vm_compute. reflexivity. Qed.
Lemma sar_fmt_nz : ~ In (Z_to_bv 8 0) (PF.pf_bytes PAI.AI_FMT).
Proof. cbn. intros H. repeat (destruct H as [H|H]; [vm_compute in H; discriminate H|]). exact H. Qed.
Lemma sar_fmt_len : Z.of_nat (length PAI.AI_FMT) = 2.
Proof. vm_compute. reflexivity. Qed.
Lemma sar_dec_len : forall v, -2^31 <= v < 2^31 -> length (PF.pf_dec v) = length (dec v).
Proof. intros v Hv. rewrite <- (PAI.ai_pf_dec v Hv). unfold PF.pf_bytes. rewrite length_map. reflexivity. Qed.
(* snprintf(b, 16, "%d", id) (0x8c868-0x8c87c) writes dec id and its terminator: the text is at most 11 bytes *)
Lemma sar_dec_text : forall v, -2^31 <= v < 2^31 ->
PF.pf_bytes (firstn (Z.to_nat (16 - 1)) (PF.pf_dec v) ++ [0]) = dec v ++ [Z_to_bv 8 0].
Proof.
intros v Hv. pose proof (dec_length v Hv) as Hl. pose proof (sar_dec_len v Hv) as Hl2.
rewrite firstn_all2 by (rewrite Hl2; change (Z.to_nat (16 - 1)) with 15%nat; lia).
unfold PF.pf_bytes in *. rewrite map_app. rewrite <- (PAI.ai_pf_dec v Hv). reflexivity.
Qed.
(* the model step (RecModel.v:165-166) as the calls build it: record(19) (0x8c854 `addi a0,zero,0x13`) opens the
   slot with no argument, then arg_s adds dec id (b, 0x8c888) and the verb (0x8c89c), each a copy of its string *)
Lemma sar_model : forall R id verb,
sup_after_reply_m R id verb = rec_record R 19 (([] ++ [sarg (Some (dec id))]) ++ [sarg verb]).
Proof. intros R id verb. reflexivity. Qed.

(* ---------- the frame's realignment (0x8c790 `andi sp,sp,-32` on the entry sp less 96) ---------- *)
Lemma sar_denot_and32 : forall E n v, ew E n = Z_to_bv 64 v -> 96 <= v < 2 ^ 64 ->
sv_denot E (SAlu ALU_AND (SOff n (-96)) (SLit (-32))) = Z_to_bv 64 (32 * ((v - 96) / 32)).
Proof.
intros E n v Hn Hv. replace (v - 96) with (v + -96) by lia.
exact (CmdSnText.snt_denot_and_m32 E n v (-96) Hn ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.
Lemma sar_denot_add0 : forall E e, sv_denot E (SAlu ALU_ADD e (SLit 0)) = sv_denot E e.
Proof.
intros E e. rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SAlu ALU_ADD e (SLit 0)))).
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E e)). f_equal.
change (U E (SAlu ALU_ADD e (SLit 0)) = U E e). rewrite U_SAlu, U_SLit. cbn [zalu_raw].
unfold zcanon, M64. rewrite (Z.mod_0_l (2 ^ 64)) by lia. rewrite Z.add_0_r.
apply Z.mod_small. pose proof (bv_unsigned_in_range 64 (sv_denot E e)) as H. unfold U. change (bv_modulus 64) with (2 ^ 64) in H. exact H.
Qed.
Lemma sar_denot_off0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma sar_sp1_facts : forall sp, sp mod 16 = 0 -> 2 ^ 46 <= sp ->
sp - 112 <= 32 * ((sp - 96) / 32) <= sp - 96 /\ (32 * ((sp - 96) / 32)) mod 32 = 0 /\
(32 * ((sp - 96) / 32) - sp) mod 16 = 0.
Proof.
intros sp H16 Hlo.
assert (H96 : (sp - 96) mod 16 = 0) by (rewrite Zminus_mod, H16; reflexivity).
destruct (CmdSnText.snt_sp1_facts (sp - 96) ltac:(lia) H96) as (H1 & H2 & H3).
split; [lia|]. split; [exact H2|].
rewrite Zminus_mod, H3, H16. reflexivity.
Qed.
Lemma sar_mod_16_8 : forall x, x mod 16 = 0 -> x mod 8 = 0.
Proof. intros x H. pose proof (Z.div_mod x 16 ltac:(lia)). rewrite H in H0. rewrite H0. replace (16 * (x / 16) + 0) with ((2 * (x / 16)) * 8) by lia. apply Z_mod_mult. Qed.

(* ---------- membership in the record's long lists, decided by computation on a closed goal ---------- *)
Lemma sar_not_in_ranges : forall (L : list (Z * Z)) lo hi,
forallb (fun r => (hi <=? fst r) || (fst r + snd r <=? lo)) L = true ->
forall a, lo <= a < hi -> ~ Exists (in_zr a) L.
Proof.
intros L lo hi HL a Ha HE. apply Exists_exists in HE as (r & Hr & Hin).
pose proof (proj1 (forallb_forall _ _) HL r Hr) as Hb. cbn beta in Hb.
apply Bool.orb_true_iff in Hb. unfold in_zr in Hin.
destruct Hb as [Hb|Hb]; apply Z.leb_le in Hb; lia.
Qed.
Definition sar_cell_is (a v : Z) (c : acell) : bool :=
  match c with
  | ACell (ANum a') (S O) (AV (ANum v')) => (a' =? a) && (v' =? v)
  | _ => false
  end.
Lemma sar_cell_in : forall a v l, existsb (sar_cell_is a v) l = true -> In (z1 (ANum a) v) l.
Proof.
intros a v l. induction l as [|c l IH]; cbn [existsb In]; [discriminate|].
intros H. apply orb_true_iff in H as [H|H]; [left | right; exact (IH H)].
destruct c as [ca cw cv]. unfold sar_cell_is in H.
destruct ca; try discriminate H. destruct cw as [|[|cw]]; try discriminate H.
destruct cv as [e|m w]; try discriminate H. destruct e; try discriminate H.
apply andb_true_iff in H as [H1 H2]. apply Z.eqb_eq in H1, H2. subst. reflexivity.
Qed.
(* the shadow bytes of the format's granule 0x21f40 and of the redzone after it (lib/B/YF0m.v Tfib_const_shadow):
   0x7fffc3e8 = 3 (the partial granule: "%d" and its terminator), 0x7fffc3e9 .. 0x7fffc3ef the redzone *)
Lemma sar_cs_3e8 : In (z1 (ANum 0x7fffc3e8) 0x3) Tfib_const_shadow.
Proof. apply sar_cell_in. vm_compute. reflexivity. Qed.
Lemma sar_cs_3e9 : In (z1 (ANum 0x7fffc3e9) 0xf9) Tfib_const_shadow.
Proof. apply sar_cell_in. vm_compute. reflexivity. Qed.
Lemma sar_cs_3ea : In (z1 (ANum 0x7fffc3ea) 0xf9) Tfib_const_shadow.
Proof. apply sar_cell_in. vm_compute. reflexivity. Qed.
Lemma sar_cs_3eb : In (z1 (ANum 0x7fffc3eb) 0xf9) Tfib_const_shadow.
Proof. apply sar_cell_in. vm_compute. reflexivity. Qed.
Lemma sar_cs_3ec : In (z1 (ANum 0x7fffc3ec) 0x6) Tfib_const_shadow.
Proof. apply sar_cell_in. vm_compute. reflexivity. Qed.
Lemma sar_cs_3ed : In (z1 (ANum 0x7fffc3ed) 0xf9) Tfib_const_shadow.
Proof. apply sar_cell_in. vm_compute. reflexivity. Qed.
Lemma sar_cs_3ee : In (z1 (ANum 0x7fffc3ee) 0xf9) Tfib_const_shadow.
Proof. apply sar_cell_in. vm_compute. reflexivity. Qed.
Lemma sar_cs_3ef : In (z1 (ANum 0x7fffc3ef) 0xf9) Tfib_const_shadow.
Proof. apply sar_cell_in. vm_compute. reflexivity. Qed.
(* the end of "%d" (0x21f42) is one of CmdRo's literal ends (CmdRo.v cmd_ro_ends, regenerated at a Theorem Labs lane 917ca7ac6b1) *)
Lemma sar_end_21f42 : In 0x21f42 cmd_ro_ends.
Proof.
assert (H : existsb (Z.eqb 0x21f42) cmd_ro_ends = true) by (vm_compute; reflexivity).
apply existsb_exists in H as (y & Hy & E). apply Z.eqb_eq in E. subst y. exact Hy.
Qed.
(* g_rec [0x5e32c0, +960) and record.spill [0x5e3760, +56) meet no runtime-owned static of the record *)
Lemma sar_grec_not_owned : forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> ~ Exists (in_zr a) Tfib_owned_static.
Proof. intros a Ha. unfold A_G_REC, REC_SIZE in Ha. apply (sar_not_in_ranges _ 0x5e32c0 0x5e3680); [vm_compute; reflexivity | lia]. Qed.
Lemma sar_spill_not_owned : forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> ~ Exists (in_zr a) Tfib_owned_static.
Proof. intros a Ha. unfold A_REC_SPILL, SC_SIZE in Ha. apply (sar_not_in_ranges _ 0x5e3760 0x5e3798); [vm_compute; reflexivity | lia]. Qed.
(* the format's three bytes are none of the record's owned statics *)
Lemma sar_fmt_not_owned : forall a, 0x21f40 <= a < 0x21f43 -> ~ Exists (in_zr a) Tfib_owned_static.
Proof. intros a Ha. apply (sar_not_in_ranges _ 0x21f40 0x21f43); [vm_compute; reflexivity | lia]. Qed.

(* ---------- the slot record() returns ---------- *)
Lemma sar_slot_range : forall R, (length (r_calls R) <= 16)%nat ->
rec_slot R mod 8 = 0 /\
((A_G_REC + OFF_CALLS <= rec_slot R /\ rec_slot R + CALL_SIZE <= A_G_REC + REC_SIZE) \/ rec_slot R = A_REC_SPILL).
Proof.
intros R Hl. unfold rec_slot. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [Hlt | Hge].
- unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE. split; [|left; lia].
  replace (6173376 + 16 + 56 * Z.of_nat (length (r_calls R))) with ((771674 + 7 * Z.of_nat (length (r_calls R))) * 8) by lia.
  apply Z_mod_mult.
- split; [reflexivity | right; reflexivity].
Qed.

(* ---------- the symbolic entry state: the stack below the entry sp (the zero word at sp0 - 96 and the saved
   registers above it), the shadow GOT word and cell, the use-after-return GOT word and flag; the realigned sp is
   atom 34 ---------- *)
Definition sar_extra (uar sp1 : Z) : list word := map (Z_to_bv 64) [SB; uar; sp1].
Definition sar_regions0 : smem := [
 YP09.mkRegion (Some 2%nat) (-96) (-88) (-96) (-88) [];
 YP09.mkRegion (Some 2%nat) (-88) 0 (-88) 0 [];
 got_regionP; bcell_regionP 32; uar_got_regionP 33; uar_cell_regionP 33 ].
Definition sar_facts0 : facts :=
mkFacts [(2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF SB SB 0); (34%nat, mkAF (2^46) (2^47) 5)] [] [].
Definition ss_sar0 : sstate := mkSS AF_sup_after_reply sr_atoms sar_regions0 None sar_facts0.
(* the frame's regions after the side-stack call (class 0, 64 bytes): its header (F + 0 .. 24 written), its flag word
   (F + 56, read only), its shadow (8 bytes) *)
Definition sar_fr_hdr : YP09.region := YP09.mkRegion (Some 1028%nat) 0 32 0 24 [].
Definition sar_fr_flg : YP09.region := YP09.mkRegion (Some 1028%nat) 56 64 56 56 [YP09.mkChunk 56 (CVal 8 (SOff 1040 0))].
Definition sar_fr_shd : YP09.region := YP09.mkRegion (Some 1041%nat) 0 8 0 8 [].
Definition sar_sp1slot : YP09.region := YP09.mkRegion (Some 34%nat) 0 8 0 8 [].
Definition sar_shx_F : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 1028 0) (SLit 3)) (SOff 32 0).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.


Section b.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Lemma sar_region_kept_hi2 : forall E H H2 (m m2 : word -> option byte) n b lo hi wlo whi cs,
bv_unsigned (ew E n) = b ->
(forall a, b + lo <= a < b + hi -> aview SEGS H2 m2 a = aview SEGS H m a) ->
(forall a, b + wlo <= a < b + whi -> apresent H2 m2 a) ->
region_kept SEGS E (mrestrict H m) (mrestrict H2 m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H H2 m m2 n b lo hi wlo whi cs Hn Hav Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hav. exact Ha.
- intros _. apply (apresent_writable SEGS). apply Hp. exact Ha.
Qed.
Lemma sar_aview_frame_pt : forall E rs H (m m' : word -> option byte) a,
frame_of E rs (mrestrict H m) (mrestrict H m') -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a ->
aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' a HF Ha Hn. apply (aview_eq_of SEGS). apply HF. rewrite unsigned_lit_small by lia. exact Hn.
Qed.

(* a word / a byte the symbolic state records in one of its regions, as the reader of the memory sees it *)
Lemma sar_word_of_region : forall E ss (H : word -> bool) ms0 i n lo hi wlo whi cs b od e v,
st_ok SEGS E ss (restrict H ms0) -> nth_error (ss_mem ss) i = Some (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal 8 e)) cs -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
rdword (aview SEGS H (ms_mem ms0)) (b + od) = Some v.
Proof.
intros E ss H ms0 i n lo hi wlo whi cs b od e v HS Hi Hn Hc He Hv.
pose proof (YN0d.st_ok_region SEGS E ss (restrict H ms0) i _ HS Hi) as HR.
pose proof (field_of_region E _ n b cs lo hi wlo whi od 8%N e v HR Hn Hc He ltac:(cbn; lia) ltac:(cbn; lia)) as HV.
apply (rdword_of_val_mem SEGS); [exact HV | exact Hv].
Qed.
Lemma sar_byte_of_region : forall E ss (H : word -> bool) ms0 i n lo hi wlo whi cs b od e v,
st_ok SEGS E ss (restrict H ms0) -> nth_error (ss_mem ss) i = Some (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal 1 e)) cs -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 256 ->
aview SEGS H (ms_mem ms0) (b + od) = Some v.
Proof.
intros E ss H ms0 i n lo hi wlo whi cs b od e v HS Hi Hn Hc He Hv.
pose proof (YN0d.st_ok_region SEGS E ss (restrict H ms0) i _ HS Hi) as HR.
pose proof (field_of_region E _ n b cs lo hi wlo whi od 1%N e v HR Hn Hc He ltac:(cbn; lia) ltac:(cbn; lia)) as HV.
exact (aview_of_val_mem1 SEGS H (ms_mem ms0) (b + od) v HV Hv).
Qed.
Section e.
Variable B : asyms.
Hypothesis HB : CmdBSyms B.
Hypothesis VOBJS : cmd_val_objs.
Hypothesis SIGP : cmd_sig_prog.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.

(* ---------- the call targets and the listing's objects ---------- *)
Local Ltac sar_in := repeat (first [left; reflexivity | right]).
Lemma sar_sig_arg_s : SIG CS_arg_s = BASE + AF_arg_s.
Proof. rewrite (SIGP CS_arg_s) by (cbv [cmd_prog_syms]; sar_in). f_equal; vm_compute; reflexivity. Qed.
(* the objects the walk's auipc pairs name (gen/funcs.tsv: 0, 1, 51, 59, 83): each pair is a PLdHi or a PAddHi on an
   object atom; nothing is loaded or stored through an A_HI value (A_HI 190-194: 0xa579c, 0xa67a0, 0x15800, 0x8c804,
   0x21868), so the walk needs no cmd_val_his. 0x8c868/0x8c86c: the format "%d" (a2 of the snprintf call) *)
Lemma sar_obj51 : VAL (A_OBJ 51) = 0x21f40.
Proof. rewrite (VOBJS 51%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.

(* ---------- the format's bytes, tail and shadow at an AR state with cmd_ro_ok ---------- *)
(* a one-byte cell of the record's constant shadow holds under AR *)
Lemma sar_cshadow : forall ly S (W : world SEGS) mem md a v,
AR SEGS B ly S W mem md -> In (z1 (ANum a) v) Tfib_const_shadow -> 0 <= v < 256 ->
rdW W mem a = Some v.
Proof.
intros ly S W mem md a v HAR Hin Hv. destruct HAR as (M & _).
pose proof (am_const _ _ _ _ M) as C. rewrite (ts_const B HB ly) in C. rewrite Forall_forall in C.
specialize (C (z1 (ANum a) v) ltac:(unfold Tfib_const; apply in_or_app; right; apply in_or_app; right; exact Hin)).
unfold cell_holds in C. cbn [c_at c_val c_w z1 c1 aeval] in C.
specialize (C 0%nat ltac:(lia)). change (Z.of_nat 0) with 0 in C. rewrite Z.add_0_r in C. rewrite C. f_equal.
unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite Z.mod_mod by lia. apply Z.mod_small. exact Hv.
Qed.
(* the format's 3 bytes ("%d" and its terminator) are addressable: the partial granule 0x21f40 at shadow 3 *)
Lemma sar_fmt_addressable : forall ly S (W : world SEGS) mem md,
AR SEGS B ly S W mem md -> range_addressable (rdW W mem) SHADOW_OFF 0x21f40 3.
Proof.
intros ly S W mem md HAR x Hx. unfold shadow_of_addr.
assert (Hq : x / 8 = 0x21f40 / 8) by (Z.div_mod_to_equations; lia). rewrite Hq.
exists 3. split.
- replace (SHADOW_OFF + 0x21f40 / 8) with 0x7fffc3e8 by (vm_compute; reflexivity).
  exact (sar_cshadow ly S W mem md _ _ HAR sar_cs_3e8 ltac:(lia)).
- right. split; [Z.div_mod_to_equations; lia | lia].
Qed.
(* every shadow byte of the format's hull (0x7fffc3e8 .. 0x7fffc3ef) is visible *)
Lemma sar_fmt_hull : forall ly S (W : world SEGS) mem md,
AR SEGS B ly S W mem md -> shadow_hull_vis (rdW W mem) 0x21f40 3.
Proof.
intros ly S W mem md HAR s Hs.
assert (E1 : shadow_addr 0x21f40 / 8 * 8 = 0x7fffc3e8) by (vm_compute; reflexivity).
assert (E2 : shadow_addr (0x21f40 + 3 - 1) / 8 * 8 + 8 = 0x7fffc3f0) by (vm_compute; reflexivity).
rewrite E1, E2 in Hs.
assert (Hs8 : s = 0x7fffc3e8 \/ s = 0x7fffc3e9 \/ s = 0x7fffc3ea \/ s = 0x7fffc3eb \/ s = 0x7fffc3ec \/
  s = 0x7fffc3ed \/ s = 0x7fffc3ee \/ s = 0x7fffc3ef) by lia.
destruct Hs8 as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]].
- rewrite (sar_cshadow ly S W mem md _ _ HAR sar_cs_3e8 ltac:(lia)). discriminate.
- rewrite (sar_cshadow ly S W mem md _ _ HAR sar_cs_3e9 ltac:(lia)). discriminate.
- rewrite (sar_cshadow ly S W mem md _ _ HAR sar_cs_3ea ltac:(lia)). discriminate.
- rewrite (sar_cshadow ly S W mem md _ _ HAR sar_cs_3eb ltac:(lia)). discriminate.
- rewrite (sar_cshadow ly S W mem md _ _ HAR sar_cs_3ec ltac:(lia)). discriminate.
- rewrite (sar_cshadow ly S W mem md _ _ HAR sar_cs_3ed ltac:(lia)). discriminate.
- rewrite (sar_cshadow ly S W mem md _ _ HAR sar_cs_3ee ltac:(lia)). discriminate.
- rewrite (sar_cshadow ly S W mem md _ _ HAR sar_cs_3ef ltac:(lia)). discriminate.
Qed.
(* the format's bytes and the visible tail word after them (CmdRo.v: RO_lit_21f40 and its end 0x21f42) *)
Lemma sar_fmt_ro : forall (W : world SEGS) mem, cmd_ro_ok (rdW W mem) ->
astr_at SEGS W mem 0x21f40 (PF.pf_bytes PAI.AI_FMT) /\ (forall a, 0x21f40 <= a < 0x21f43 -> rdW W mem a <> None) /\
atail_vis SEGS W mem (0x21f40 + Z.of_nat (length PAI.AI_FMT)).
Proof.
intros W mem HRO.
assert (Hb : abytes_atR (rdW W mem) 0x21f40 RO_lit_21f40).
{ pose proof HRO as [H _]. unfold cmd_ro_bytes in H. sar_projz H 0x21f40. }
split; [|split].
- split; [|exact sar_fmt_nz]. apply (abytes_atR_view SEGS). rewrite sar_fmt_bytes. exact Hb.
- intros a Ha. replace a with (0x21f40 + Z.of_nat (Z.to_nat (a - 0x21f40))) by lia.
  rewrite (Hb (Z.to_nat (a - 0x21f40))) by (change (length RO_lit_21f40) with 3%nat; lia). discriminate.
- rewrite sar_fmt_len. intros a Ha. destruct HRO as [_ HT]. exact (HT 0x21f42 sar_end_21f42 a Ha).
Qed.
(* the format as the printf chain reads it (RtPFShared.v:64 fmt_at), over any regions the run writes that lie above
   the literal *)
Lemma sar_fmt_at : forall ly S (W : world SEGS) mem md rs, AR SEGS B ly S W mem md -> cmd_ro_ok (rdW W mem) ->
Forall (fun r => fst r + snd r <= 0x21f40 \/ 0x21f43 <= fst r) rs ->
RtPFShared.fmt_at (rdW W mem) rs 0x21f40 PAI.AI_FMT.
Proof.
intros ly S W mem md rs HAR HRO Hrs.
assert (Hb : abytes_atR (rdW W mem) 0x21f40 RO_lit_21f40).
{ pose proof HRO as [H _]. unfold cmd_ro_bytes in H. sar_projz H 0x21f40. }
split; [lia|]. split.
- intros i Hi. change (Z.of_nat (length PAI.AI_FMT)) with 2 in Hi.
  replace (0x21f40 + i) with (0x21f40 + Z.of_nat (Z.to_nat i)) by lia.
  rewrite (Hb (Z.to_nat i) ltac:(change (length RO_lit_21f40) with 3%nat; lia)). f_equal.
  assert (Hc : (Z.to_nat i = 0 \/ Z.to_nat i = 1 \/ Z.to_nat i = 2)%nat) by lia.
  destruct Hc as [-> | [-> | ->]]; vm_compute; reflexivity.
- change (Z.of_nat (length PAI.AI_FMT)) with 2.
  split; [apply Forall_impl with (2 := Hrs); intros r Hr; unfold zdisjoint; cbn [fst snd]; lia|].
  split; [unfold amem_range, kLowMemEnd; left; lia|].
  change (2 + 1) with 3.
  split; [exact (sar_fmt_addressable ly S W mem md HAR) | exact (sar_fmt_hull ly S W mem md HAR)].
Qed.

(* ---------- the read-only words the printf chain reads (CMD_SNP_CR), by computation on the closed lists ---------- *)
Lemma sar_ranges_bnds : forall (L : list (Z * Z)) lo hi,
forallb (fun r => (lo <=? fst r) && (fst r + snd r <=? hi)) L = true ->
Forall (fun r => lo <= fst r /\ fst r + snd r <= hi) L.
Proof.
intros L lo hi H. apply Forall_forall. intros r Hr.
pose proof (proj1 (forallb_forall _ _) H r Hr) as Hb. apply andb_true_iff in Hb as [H1 H2].
apply Z.leb_le in H1, H2. split; [exact H1 | exact H2].
Qed.
Lemma sar_ranges_bounded : forall (L : list (Z * Z)),
forallb (fun r => (0 <=? fst r) && (fst r + snd r <=? 2 ^ 63)) L = true ->
Forall (fun r => 0 <= fst r /\ fst r + snd r <= 2 ^ 63) L.
Proof.
intros L H. apply Forall_forall. intros r Hr.
pose proof (proj1 (forallb_forall _ _) H r Hr) as Hb. apply andb_true_iff in Hb as [H1 H2].
apply Z.leb_le in H1, H2. split; [exact H1 | exact H2].
Qed.
Lemma sar_ranges_in : forall (L : list (Z * Z)) lo hi,
forallb (fun r => (lo <=? fst r) && (fst r + snd r <=? hi)) L = true ->
forall a, Exists (in_zr a) L -> lo <= a < hi.
Proof.
intros L lo hi H a Hex. apply Exists_exists in Hex as (r & Hr & Hin).
pose proof (proj1 (forallb_forall _ _) H r Hr) as Hb. apply andb_true_iff in Hb as [H1 H2].
apply Z.leb_le in H1, H2. unfold in_zr in Hin. lia.
Qed.
Lemma sar_ranges_disj : forall (L : list (Z * Z)) hi (rs : list (Z * Z)),
forallb (fun r => fst r + snd r <=? hi) L = true -> Forall (fun s => hi <= fst s) rs ->
Forall (fun r => Forall (zdisjoint r) rs) L.
Proof.
intros L hi rs H Hrs. apply Forall_forall. intros r Hr.
pose proof (proj1 (forallb_forall _ _) H r Hr) as Hb. apply Z.leb_le in Hb.
apply Forall_impl with (2 := Hrs). intros s Hs. unfold zdisjoint. left. lia.
Qed.
Lemma sar_disj_lists : forall (L1 L2 : list (Z * Z)),
forallb (fun r => forallb (fun s => (fst r + snd r <=? fst s) || (fst s + snd s <=? fst r)) L2) L1 = true ->
forall a, Exists (in_zr a) L1 -> ~ Exists (in_zr a) L2.
Proof.
intros L1 L2 H a He1 He2.
apply Exists_exists in He1 as (r & Hr & Hin1). apply Exists_exists in He2 as (s & Hs & Hin2).
pose proof (proj1 (forallb_forall _ _) H r Hr) as Hb.
pose proof (proj1 (forallb_forall _ _) Hb s Hs) as Hb2.
apply orb_true_iff in Hb2 as [Hb2 | Hb2]; apply Z.leb_le in Hb2; unfold in_zr in Hin1, Hin2; lia.
Qed.

(* ---------- the decimal text snprintf writes, as the recorder's bytes ---------- *)
Lemma sar_pf_digits_chars : forall fuel x acc, 0 <= x -> Forall (fun c => 0 <= c < 256) acc ->
Forall (fun c => 0 <= c < 256) (PF.pf_digits fuel x acc).
Proof.
induction fuel as [|fuel IH]; intros x acc Hx Ha; cbn [PF.pf_digits]; [exact Ha|].
destruct (Z.ltb_spec x 10) as [Hlt | Hge]; [apply Forall_cons; [lia | exact Ha]|].
apply IH; [apply Z.div_pos; lia|]. apply Forall_cons; [pose proof (Z.mod_pos_bound x 10 ltac:(lia)); lia | exact Ha].
Qed.
Lemma sar_dec_chars : forall v, Forall (fun c => 0 <= c < 256) (PF.pf_dec v).
Proof.
intros v. unfold PF.pf_dec. destruct (Z.ltb_spec v 0) as [Hv | Hv].
- apply Forall_cons; [lia | apply sar_pf_digits_chars; [lia | apply Forall_nil]].
- apply sar_pf_digits_chars; [lia | apply Forall_nil].
Qed.
(* what the snprintf post leaves at b (the Z-valued text) is the recorder's string dec id *)
Lemma sar_dec_bridge : forall (rd : reader) a v, -2 ^ 31 <= v < 2 ^ 31 ->
(forall i, 0 <= i < Z.of_nat (length (PF.pf_dec v)) + 1 ->
 rd (a + i) = Some (nth (Z.to_nat i) (PF.pf_dec v ++ [0]) 0)) ->
astr_atR rd a (dec v).
Proof.
intros rd a v Hv Hrd. split; [|exact (dec_no0 v)].
intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
pose proof (sar_dec_len v Hv) as Hl.
rewrite (Hrd (Z.of_nat i) ltac:(lia)), Nat2Z.id. f_equal.
assert (Hd : dec v ++ [Z_to_bv 8 0] = map (fun c => Z_to_bv 8 c) (PF.pf_dec v ++ [0])).
{ rewrite map_app. cbn [map]. rewrite <- (PAI.ai_pf_dec v Hv). reflexivity. }
rewrite Hd, (map_nth (fun c => Z_to_bv 8 c) (PF.pf_dec v ++ [0]) 0 i).
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
symmetry. apply Z.mod_small.
assert (Hall : Forall (fun c => 0 <= c < 256) (PF.pf_dec v ++ [0]))
  by (apply Forall_app; split; [exact (sar_dec_chars v) | apply Forall_cons; [lia | apply Forall_nil]]).
destruct (Nat.lt_ge_cases i (length (PF.pf_dec v ++ [0]))) as [Hlt | Hge].
- rewrite Forall_forall in Hall. exact (Hall _ (nth_In _ 0 Hlt)).
- rewrite nth_overflow by exact Hge. lia.
Qed.

(* ---------- the recorder's state survives writes outside g_rec, record.spill and its own blocks ---------- *)
Lemma sar_aval_mem_kept : forall (rd rd' : reader) a n v, aval_mem rd a n v ->
(forall k, (k < n)%nat -> rd' (a + Z.of_nat k) = rd (a + Z.of_nat k)) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H Hk k Hkn. rewrite (Hk k Hkn). exact (H k Hkn). Qed.
Lemma sar_rabytes_kept : forall (rd rd' : reader) a l, abytes_atR rd a l ->
(forall i, 0 <= i < Z.of_nat (length l) -> rd' (a + i) = rd (a + i)) -> abytes_atR rd' a l.
Proof. intros rd rd' a l H Hk i Hi. rewrite (Hk (Z.of_nat i) ltac:(lia)). exact (H i Hi). Qed.
Lemma sar_rastr_kept : forall (rd rd' : reader) a s, astr_atR rd a s ->
(forall i, 0 <= i < Z.of_nat (length s) + 1 -> rd' (a + i) = rd (a + i)) -> astr_atR rd' a s.
Proof.
intros rd rd' a s [H1 H2] Hk. split; [|exact H2]. apply (sar_rabytes_kept rd); [exact H1|].
intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply Hk. lia.
Qed.
Lemma sar_acall_at_kept : forall bl bl' (rd rd' : reader) a c P, acall_at bl rd a c P ->
(forall pn, In pn P -> In pn bl') ->
(forall i, 0 <= i < CALL_OFF_ARGS + 8 * Z.of_nat (length (snd c)) -> rd' (a + i) = rd (a + i)) ->
(forall pn i, In pn P -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
acall_at bl' rd' a c P.
Proof.
intros bl bl' rd rd' a c P (H1 & H2 & H3 & H4 & H5 & H6 & H7) Hbl Ha Hp.
unfold acall_at. unfold CALL_OFF_ARGS, CALL_OFF_FN, CALL_OFF_NARGS in *.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
split; [apply (sar_aval_mem_kept rd); [exact H4 | intros k Hk; rewrite <- Z.add_assoc; apply Ha; apply Nat2Z.inj_lt in Hk; change (Z.of_nat 4) with 4 in Hk; clear - Hk; pose proof (Nat2Z.is_nonneg (length (snd c))); lia]|].
split; [apply (sar_aval_mem_kept rd); [exact H5 | intros k Hk; rewrite <- Z.add_assoc; apply Ha; apply Nat2Z.inj_lt in Hk; change (Z.of_nat 4) with 4 in Hk; clear - Hk; pose proof (Nat2Z.is_nonneg (length (snd c))); lia]|].
split; [exact H6|].
intros k s pn Hs Hpn. destruct (H7 k s pn Hs Hpn) as (G1 & G2 & G3 & G4 & G5).
pose proof (proj1 (nth_error_Some (snd c) k) ltac:(rewrite Hs; discriminate)) as Hk.
split; [apply (sar_aval_mem_kept rd); [exact G1 | intros j Hj; rewrite <- !Z.add_assoc; apply Ha; lia]|].
split; [exact G2|]. split; [apply Hbl; exact (nth_error_In _ _ Hpn)|]. split; [exact G4|].
apply (sar_rastr_kept rd); [exact G5 | intros i Hi; apply Hp; [exact (nth_error_In _ _ Hpn) | lia]].
Qed.
Lemma sar_pair_eq_dec : forall x y : Z * Z, {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Qed.
Lemma sar_nodup_of_pairwise : forall (l : list (Z * Z)) (f : Z * Z -> Z * Z),
pairwise zdisjoint (map f l) -> (forall x, In x l -> 0 < snd (f x)) -> List.NoDup l.
Proof.
induction l as [|x t IH]; intros f Hp Hpos; [constructor|].
constructor.
- intros Hin. apply in_split in Hin as (t1 & t2 & Et).
assert (Hd : zdisjoint (f x) (f x)).
{ apply (pairwise_zdisjoint_split (map f (x :: t)) (f x) (f x) Hp).
exists [], (map f t1), (map f t2). left. rewrite Et. cbn. rewrite map_app. reflexivity. }
pose proof (Hpos x (or_introl eq_refl)). unfold zdisjoint in Hd. lia.
- apply (IH f); [| intros y Hy; apply Hpos; right; exact Hy].
change (map f (x :: t)) with ([f x] ++ map f t) in Hp. exact (proj2 (pairwise_app_l _ _ _ Hp)).
Qed.
Lemma sar_rec_repA_in : forall ly S rd R O, rec_repA B ly S rd R O -> forall pn, In pn O -> In pn (ablocks B ly S).
Proof. intros ly S rd R O (Q & HA & HO) pn Hpn. exact (lay_blocks_in _ _ _ _ _ _ HA pn (proj1 (HO pn) Hpn)). Qed.
Lemma sar_rec_repA_kept : forall ly S rd ly' S' rd' R O, rec_repA B ly S rd R O ->
(forall pn, In pn O -> In pn (ablocks B ly' S')) ->
(forall a, A_G_REC <= a < A_G_REC + 960 -> rd' a = rd a) ->
(forall a, A_REC_SPILL <= a < A_REC_SPILL + 56 -> rd' a = rd a) ->
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
unfold OFF_NCALLS, OFF_CALLS, OFF_ANSWER, OFF_REPLY, OFF_REPLY_SIZE, OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_STATE, OFF_HOST, CALL_SIZE in *.
split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
split.
{ split; [exact C1|]. split; [exact C2|].
split; [apply (sar_aval_mem_kept rd); [exact C3 | intros k Hk; apply Hg; lia]|].
split.
- intros i c P Hc Hp. destruct (C4 i c P Hc Hp) as [HC HF]. split; [|exact HF].
pose proof (proj1 (nth_error_Some (r_calls R) i) ltac:(rewrite Hc; discriminate)) as Hi.
pose proof HC as (_ & HL6 & _).
apply (sar_acall_at_kept (ablocks B ly S) _ rd); [exact HC | | |].
+ intros pn Hpn. apply HblQ. apply in_app_iff. left. apply in_concat. exists P. split; [exact (nth_error_In _ _ Hp) | exact Hpn].
+ intros j Hj. rewrite <- !Z.add_assoc. apply Hg. unfold CALL_OFF_ARGS in Hj. lia.
+ intros pn j Hpn Hj. apply HbQ; [|exact Hj]. apply in_app_iff. left. apply in_concat. exists P. split; [exact (nth_error_In _ _ Hp) | exact Hpn].
- split; [|exact C6].
pose proof C5 as (_ & HL6 & _).
apply (sar_acall_at_kept (ablocks B ly S) _ rd); [exact C5 | | |].
+ intros pn Hpn. apply HblQ. apply in_app_iff. right. apply in_app_iff. left. exact Hpn.
+ intros j Hj. apply Hs. unfold CALL_OFF_ARGS in Hj. lia.
+ intros pn j Hpn Hj. apply HbQ; [|exact Hj]. apply in_app_iff. right. apply in_app_iff. left. exact Hpn. }
split.
{ destruct (r_answer R) as [x|], (l_answer Q) as [q|]; try contradiction.
- destruct Ha as (A1 & A2 & A3 & A4 & A5 & A6).
assert (Hq : In q (concat (l_calls Q) ++ l_spill Q ++ oblk (Some q) ++ oblk (l_reply Q)))
by (apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left; left; reflexivity).
split; [apply (sar_aval_mem_kept rd); [exact A1 | intros k Hk; apply Hg; lia]|].
split; [exact A2|]. split; [apply HblQ; exact Hq|]. split; [exact A4|].
split; [apply (sar_rastr_kept rd); [exact A5 | intros i Hi; apply HbQ; [exact Hq | lia]] | exact A6].
- apply (sar_aval_mem_kept rd); [exact Ha | intros k Hk; apply Hg; lia]. }
split.
{ destruct (r_reply R) as [x|], (l_reply Q) as [q|]; try contradiction.
- destruct Hr as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
assert (Hq : In q (concat (l_calls Q) ++ l_spill Q ++ oblk (l_answer Q) ++ oblk (Some q)))
by (apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; right; left; reflexivity).
split; [apply (sar_aval_mem_kept rd); [exact A1 | intros k Hk; apply Hg; lia]|].
split; [apply (sar_aval_mem_kept rd); [exact A2 | intros k Hk; apply Hg; lia]|].
split; [exact A3|]. split; [exact A4|]. split; [apply HblQ; exact Hq|]. split; [exact A6|].
split; [apply (sar_rabytes_kept rd); [exact A7 | intros i Hi; apply HbQ; [exact Hq | lia]] | exact A8].
- destruct Hr as [A1 A2]. split; apply (sar_aval_mem_kept rd); first [exact A1 | exact A2 | intros k Hk; apply Hg; lia]. }
split; [|exact Hown].
split; [apply (sar_aval_mem_kept rd); [exact S1 | intros k Hk; apply Hg; lia]|].
split; [apply (sar_aval_mem_kept rd); [exact S2 | intros k Hk; apply Hg; lia]|].
split; [apply (sar_aval_mem_kept rd); [exact S3 | intros k Hk; apply Hg; lia]|].
split; [apply (sar_aval_mem_kept rd); [exact S4 | intros k Hk; apply Hg; lia]|].
split; [apply (sar_aval_mem_kept rd); [exact S5 | intros k Hk; apply Hg; lia]|].
exact S6.
Qed.
Lemma sar_ablocks_nodup : forall ly S W mem md, AR SEGS B ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
intros ly S W mem md HAR. destruct (al_sep _ _ LAWS ly S W mem md HAR) as [Hp _]. apply pairwise_app_l in Hp as [Hp _].
apply (sar_nodup_of_pairwise _ (fun b0 : Z * Z => (fst b0, req_size (snd b0))) Hp).
intros [p n] Hin. cbn [fst snd]. destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
unfold req_size. destruct (Z.eqb_spec n 0); lia.
Qed.
End e.

(* ---------- the entry state's seed ---------- *)
Section c2.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
(* any stack bound of at least the frame and the realignment (SUP_AFTER_REPLY_STK, sup_after_reply_c.v, is one) *)
Lemma sar_entry : forall STK W ly S regs mem md ch, 112 <= STK ->
afn_pre SEGS B STK ly S W regs mem md ch ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (sar_extra (as_uar_cell B) (32 * ((spZ regs - 96) / 32))))) ss_sar0
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_sup_after_reply)) mem (seg_rom SEGS))).
Proof.
intros STK W ly S regs mem md ch HSTK HPRE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
rewrite (palf_got_uar B TLF) in Kguar.
pose proof (palf_uar_img B TLF) as Huar. pose proof (palf_sep B TLF) as Hsep. cbn [zseps zseps_from fst snd] in Hsep.
pose proof (pa_obj_img 0 ltac:(lia)) as HO0. pose proof (pa_obj_img 1 ltac:(lia)) as HO1. pose proof (pa_obj_img 12 ltac:(lia)) as HO12.
rewrite restrict_mkst_fx.
set (sp1 := 32 * ((spZ regs - 96) / 32)).
destruct (sar_sp1_facts (spZ regs) Hal16 ltac:(lia)) as (Hsp1 & Hsp1a & Hsp1b). fold sp1 in Hsp1, Hsp1a, Hsp1b.
set (E := Eimg (Ereg regs (sar_extra (as_uar_cell B) sp1))).
assert (Usp : bv_unsigned (ew E 2) = spZ regs).
{ subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl). reflexivity. }
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (as_uar_cell B)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 sp1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E242 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (U0 : base_val E (Some (A_OBJ 0)) = VAL (A_OBJ 0)) by (apply VB; [exact E241 | lia]).
assert (U1 : base_val E (Some (A_OBJ 1)) = VAL (A_OBJ 1)) by (apply VB; [exact E242 | lia]).
assert (U12 : base_val E (Some (A_OBJ 12)) = VAL (A_OBJ 12)) by (apply VB; [exact E253 | lia]).
assert (U33 : base_val E (Some 33%nat) = as_uar_cell B) by (apply VB; [exact E33 | lia]).
assert (U2 : base_val E (Some 2%nat) = spZ regs) by (cbn [base_val]; exact Usp).
unfold ss_sar0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold sar_regions0, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
+ rewrite U2. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
+ rewrite U2. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
+ rewrite U0. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
[rewrite sar_denot_off0; exact E253 | lia | lia |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
+ rewrite U12. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SB);
[rewrite sar_denot_off0; exact E32 | unfold SB; lia | lia |].
rewrite Z.add_0_r. rewrite SB_SHADOW_OFF. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
+ rewrite U1. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff 33 0) (as_uar_cell B));
[rewrite sar_denot_off0; exact E33 | lia | lia |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kguar).
+ rewrite U33. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (as_uar_cell B) 0 4 (SLit 1) 1); [reflexivity | lia | lia |].
rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) mem _ _ Kuar).
- apply pairwise_disjoint_of_extents. unfold sar_regions0, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite U2, U0, U1, U12, U33.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
repeat split; lia.
- split; [|split; [exact I | exact I]].
cbn [sar_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E32, E34, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 5) with 32. rewrite Z.pow_0_r, Z.mod_1_r.
rewrite Hal16, Hsp1a. unfold SB. repeat split; lia.
Qed.
End c2.
End b.
End a.

(* the frame chain at a call whose s0 is the caller's frame pointer sp0 (the entry sp), from afn_pre's chain at sp0:
   achain_push with the frame record the prologue stored (ra at sp0 - 8, the caller's s0 at sp0 - 16); a frame at
   the very top of the stack (sp0 >= ly_top - 16) has the empty chain *)
Section ch. Context {rc : YM05.RunCeil}.
Lemma sar_chain_at : forall ly (rd rd' : reader) sp0 s0 ra ch sp,
achain ly rd sp0 s0 ch -> ly_top ly <= 2 ^ 64 -> sp0 <= ly_top ly ->
(forall a, sp0 <= a < 2 ^ 64 -> rd' a = rd a) ->
rdword rd' (sp0 - 8) = Some ra -> rdword rd' (sp0 - 16) = Some s0 -> 4096 <= ra ->
alloc_ceiling <= sp0 -> sp0 mod 8 = 0 -> sp + 16 <= sp0 ->
exists ch', achain ly rd' sp sp0 ch'.
Proof.
intros ly rd rd' sp0 s0 ra ch sp Hch Htop Hle Hk H8 H16 Hra Hc Hal Hsp.
destruct (Z_lt_le_dec sp0 (ly_top ly - 16)) as [Hlt | Hge].
- exists ((sp0, ra, s0) :: ch). exact (achain_push ly rd rd' sp0 s0 ra ch sp Hch Htop Hk H8 H16 Hra Hc Hal Hlt Hsp).
- exists []. left. split; [right; left; lia | reflexivity].
Qed.
End ch.

(* the region of the symbolic state at atom n that holds a word: tried at the first eight positions *)
Ltac sar_wfind HS E H ms n :=
  first [ eapply (sar_word_of_region E _ H ms 0%nat n); [exact HS | reflexivity | idtac ..]
        | eapply (sar_word_of_region E _ H ms 1%nat n); [exact HS | reflexivity | idtac ..]
        | eapply (sar_word_of_region E _ H ms 2%nat n); [exact HS | reflexivity | idtac ..]
        | eapply (sar_word_of_region E _ H ms 3%nat n); [exact HS | reflexivity | idtac ..]
        | eapply (sar_word_of_region E _ H ms 4%nat n); [exact HS | reflexivity | idtac ..]
        | eapply (sar_word_of_region E _ H ms 5%nat n); [exact HS | reflexivity | idtac ..]
        | eapply (sar_word_of_region E _ H ms 6%nat n); [exact HS | reflexivity | idtac ..]
        | eapply (sar_word_of_region E _ H ms 7%nat n); [exact HS | reflexivity | idtac ..] ].
Ltac sar_bfind HS E H ms n :=
  first [ eapply (sar_byte_of_region E _ H ms 0%nat n); [exact HS | reflexivity | idtac ..]
        | eapply (sar_byte_of_region E _ H ms 1%nat n); [exact HS | reflexivity | idtac ..]
        | eapply (sar_byte_of_region E _ H ms 2%nat n); [exact HS | reflexivity | idtac ..]
        | eapply (sar_byte_of_region E _ H ms 3%nat n); [exact HS | reflexivity | idtac ..]
        | eapply (sar_byte_of_region E _ H ms 4%nat n); [exact HS | reflexivity | idtac ..]
        | eapply (sar_byte_of_region E _ H ms 5%nat n); [exact HS | reflexivity | idtac ..]
        | eapply (sar_byte_of_region E _ H ms 6%nat n); [exact HS | reflexivity | idtac ..]
        | eapply (sar_byte_of_region E _ H ms 7%nat n); [exact HS | reflexivity | idtac ..] ].
