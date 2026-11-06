(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the trim loop of the inlined words_of in LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86800 .. 0x86858, back to its head or on to 0x868bc), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_s43.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACbk.v (a seed, the symbolic engine's runs and their branches) and A/ACfj.v (rt_G_allX: a loop by induction on its counter), over the plain proof's lib/Prog/SlotWordsRun.v sw_trim. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YI67.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaSB CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
rec_clear_c send_message_c check_reply_c check_arity_c check_words_c check_refusal_c check_round_trip_c
verbs_receive_c LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s01
LLVMFuzzerTestOneInput_s40 LLVMFuzzerTestOneInput_s49 LLVMFuzzerTestOneInput_s42.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require SlotSpec HarnessProps SlotWords SlotWordsRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs StrFun.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Local Open Scope Z_scope.

(* The trim loop (listing offsets from BASE = 0x86530), s7 = j - 1 the index of the byte the round tests:
     0x2d0  ld a1,120(sp) (text); a0 = text + s7; UBSan's three tests of text + s7 (0x2d8 overflow, 0x2e8 the
            null-ness xor, 0x2ec text null: decided by the seed's condition and ranges)
     0x2f0  srli/add/lb  the shadow byte of a0; `bnez` to the slow check 0x330 (the shadow entry makes both vanish)
     0x300  lbu a2,0(a0) the byte; `bltu s11,a2` (s11 = 32) on to 0x384: a byte above 32 is not trailing
     0x308  srl/andi     bit a2 of the mask s2; `beqz` on to 0x384: not trailing
     0x314  UBSan's null test of a0 (decided); lb, bnez the shadow byte again (vanishes); s7 -= 1; `sb zero,0(a0)`
     0x328  `bne s7,s0` (s0 = -1) back to 0x2d0, else 0x348: a2 = 0, 0x388: a2 += 1, on to 0x38c = AW_J
     0x384  a2 = s7 + 1, 0x388: a2 += 1, on to AW_J.
   One pass is one induction step on j (the plain proof's sw_trim); each run starts from the seed below: the frame
   word 120(sp) (atom 32 = text), atom 33 = text + s7 (the alias of the add, with UBSan's no-wrap condition), atom 34
   = the byte, the one region the pass reads and writes. *)

(* ---- the text buffer during the loop (the plain proof's tz) ---- *)
Lemma tl_tz_ge : forall U j i, (j <= i <= length U)%nat -> nth_error (SlotWordsRun.tz U j) i = Some (Z_to_bv 8 0).
Proof.
intros U j i H. unfold SlotWordsRun.tz. rewrite nth_error_app2 by (rewrite firstn_length_le by lia; lia).
rewrite firstn_length_le by lia. apply nth_error_repeat. lia.
Qed.
Lemma tl_nth : forall {A} (l : list A) n x d, nth_error l n = Some x -> nth n l d = x.
Proof. intros A l n x d H. apply nth_error_nth. exact H. Qed.
(* the store of a 0 at byte j turns tz U (j + 1) into tz U j *)
Lemma tl_tz_store : forall (rd rd' : reader) text U j,
  (S j <= length U)%nat -> 0 <= text -> text + Z.of_nat (length U) + 1 <= 2 ^ 64 ->
  abytes_atR rd text (SlotWordsRun.tz U (S j)) ->
  (forall x, 0 <= x < 2 ^ 64 -> x <> text + Z.of_nat j -> rd' x = rd x) -> rd' (text + Z.of_nat j) = Some 0 ->
  abytes_atR rd' text (SlotWordsRun.tz U j).
Proof.
intros rd rd' text U j Hj Ht Hhi H HK H0 i Hi.
rewrite SlotWordsRun.tz_len in Hi by lia.
destruct (Nat.eq_dec i j) as [->|Hne].
- rewrite H0, (tl_nth _ _ _ _ (tl_tz_ge U j j ltac:(lia))). reflexivity.
- rewrite HK by lia. rewrite (H i ltac:(rewrite SlotWordsRun.tz_len by lia; lia)).
  assert (E : nth_error (SlotWordsRun.tz U (S j)) i = nth_error (SlotWordsRun.tz U j) i).
  { destruct (Nat.lt_ge_cases i j) as [Hlt|Hge].
    - rewrite !SlotWordsRun.tz_nth_lt by lia. reflexivity.
    - rewrite !tl_tz_ge by lia. reflexivity. }
  destruct (nth_error (SlotWordsRun.tz U j) i) as [v|] eqn:Ev.
  + rewrite (tl_nth _ _ _ _ E), (tl_nth _ _ _ _ Ev). reflexivity.
  + apply nth_error_None in Ev. rewrite SlotWordsRun.tz_len in Ev by lia. lia.
Qed.
(* a one-byte field from a byte *)
Lemma tl_le_byte1_loc : forall v, 0 <= v < 256 -> le_byte v 1 0 = v.
Proof.
intros v Hv. unfold le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. rewrite (Z.mod_small v 256) by lia. apply Z.mod_small. lia.
Qed.
Lemma tl_aval1_loc : forall (rd : reader) a v, rd a = Some v -> 0 <= v < 256 -> aval_mem rd a 1 v.
Proof.
intros rd a v H Hv k Hk. assert (k = 0%nat) by lia. subst k. replace (a + Z.of_nat 0) with a by lia. rewrite H.
rewrite (tl_le_byte1_loc v Hv). reflexivity.
Qed.
(* the mask test of 0x86838 .. 0x86840, through the engine's term for it (s2 = the mask, a2 = the byte, atom 34) *)
Lemma tl_mask_U : forall E b, ew E 34 = Z_to_bv 64 b -> 0 <= b <= 32 ->
  U E (SAlu ALU_AND (SAlu ALU_SRL (SLit 4294977024) (SOff 34 0)) (SLit 1)) =
  if SlotWords.sw_trail_z b then 1 else 0.
Proof.
intros E b H Hb. rewrite U_and_lit by lia. rewrite U_SAlu. cbn [zalu_raw].
rewrite U_lit by lia. rewrite (U_atom E 34 b H) by lia.
change 63 with (Z.ones 6). rewrite Z.land_ones by lia. change (2 ^ 6) with 64.
assert (Hs : 0 <= b mod 64 < 64) by (apply Z.mod_pos_bound; lia).
rewrite zcanon_id.
- apply SlotWords.sw_trail_mask. exact Hb.
- rewrite Z.shiftr_div_pow2 by lia. unfold M64. split; [apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]|].
  apply (Z.le_lt_trans _ 4294977024); [|lia]. apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia|].
  assert (H1 : 2 ^ 0 <= 2 ^ (b mod 64)) by (apply Z.pow_le_mono_r; lia). change (2 ^ 0) with 1 in H1.
  set (t := 2 ^ (b mod 64)) in *. clearbody t.
  replace 4294977024 with (1 * 4294977024) at 1 by reflexivity. apply Z.mul_le_mono_nonneg_r; lia.
Qed.
(* the latch `bne s7,s0` (0x86858): s7 = j - 1 after the decrement, s0 = -1 *)
Lemma tl_ne_U : forall E v, ew E 23 = Z_to_bv 64 v -> 0 <= v < 2 ^ 63 -> bv_unsigned (ew E 8) = 2 ^ 64 - 1 ->
  branch_taken BC_NE (sv_denot E (SOff 23 (-1))) (sv_denot E (SOff 8 0)) = negb (v =? 0).
Proof.
intros E v H23 Hv H8. rewrite branch_ne_U, !U_SOff, H23, H8, unsigned_lit_small by lia.
rewrite (zcanon_small (2 ^ 64 - 1 + 0)) by lia.
destruct (Z.eq_dec v 0) as [->|Hne]; [reflexivity|].
rewrite (zcanon_small (v + -1)) by lia.
rewrite (proj2 (Z.eqb_neq (v + -1) (2 ^ 64 - 1 + 0))) by lia. rewrite (proj2 (Z.eqb_neq v 0)) by exact Hne.
reflexivity.
Qed.

(* ---- the seed at 0x86800 ---- *)
Definition TLx : sv := SOff 25 0.
Definition TLspan : Z * Z := (LT_SB, LT_SB + 2 ^ 44 - 1).
Definition tl_fr : YP09.region := YP09.mkRegion (Some 2%nat) 0 256 0 0 [YP09.mkChunk 120 (CVal 8 (SOff 32 0))].
Definition tl_tx : YP09.region := YP09.mkRegion (Some 33%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SOff 34 0))].
Definition tl_facts : facts :=
  mkFacts [ (25%nat, mkAF LT_SB LT_SB 0); (32%nat, mkAF 4096 (2 ^ 47 - 1) 0); (33%nat, mkAF 4096 (2 ^ 47 - 1) 0);
            (34%nat, mkAF 0 255 0) ]
    [ mkAC BC_GEU (SOff 33 0) (SOff 32 0) ]
    [ (SAlu ALU_ADD (SOff 32 0) (SOff 23 0), SOff 33 0) ].
Definition tl_sregs : list sv := sr_set (sr_set sr_atoms (27%bv : bv 5) (SLit 32)) (18%bv : bv 5) (SLit LT_MASK).
Definition ss_tl : sstate := mkSS AW_T tl_sregs [tl_fr; tl_tx] None tl_facts.
Definition tl_SH : list shent := [mkSHE 33 0 1].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the seed's environment: the registers, then atoms 32 = text, 33 = text + s7, 34 = the byte *)
Definition tl_E (regs : bvmap 5 word) (t e b : Z) : env := Eimg (Ereg regs [Z_to_bv 64 t; Z_to_bv 64 e; Z_to_bv 64 b]).
Lemma tl_E_lo : forall regs t e b n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (tl_E regs t e b) n = getr regs r.
Proof.
intros regs t e b n r Hr. pose proof (u5_range r) as R5. unfold tl_E. rewrite Eimg_low by (unfold A_TEXT; lia).
apply ew_Ereg_nat. exact Hr.
Qed.
Lemma tl_E_32 : forall regs t e b, ew (tl_E regs t e b) 32 = Z_to_bv 64 t.
Proof. intros regs t e b. unfold tl_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). Qed.
Lemma tl_E_33 : forall regs t e b, ew (tl_E regs t e b) 33 = Z_to_bv 64 e.
Proof. intros regs t e b. unfold tl_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 1). Qed.
Lemma tl_E_34 : forall regs t e b, ew (tl_E regs t e b) 34 = Z_to_bv 64 b.
Proof. intros regs t e b. unfold tl_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 2). Qed.
Lemma tl_E_agree : forall regs t e b, env_agree 32 (Ereg regs [Z_to_bv 64 t; Z_to_bv 64 e; Z_to_bv 64 b]) (tl_E regs t e b).
Proof. intros regs t e b. split; [intros n Hn; unfold tl_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]. Qed.

Lemma tl_val_of_aval : forall H (mem : word -> option byte) a n v,
  aval_mem (aview SEGS H mem) a n v -> val_mem SEGS (mrestrict H mem) a n v.
Proof.
intros H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte SEGS (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Eb; cbn in Hv; [|discriminate Hv].
injection Hv as Hb. rewrite <- (Z_to_bv_bv_unsigned 8 b). rewrite Hb. reflexivity.
Qed.

(* the byte of the state's text region (its second region, its chunk at offset 0), read back *)
Lemma tl_chunk_byte : forall (W : world SEGS) E ss ms rg e v a,
  st_ok SEGS E ss (restrict (w_H W) ms) -> nth_error (ss_mem ss) 1 = Some rg -> YP09.r_base rg = Some 33%nat ->
  In (YP09.mkChunk 0 (CVal 1 e)) (YP09.r_chunks rg) -> bv_unsigned (ew E 33) = a ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 256 ->
  rdW W (ms_mem ms) a = Some v.
Proof.
intros W E ss ms rg e v a HS Hi Hb Hin Ha He Hv.
pose proof (YI67.st_chunk_val SEGS E ss (restrict (w_H W) ms) 1 rg 33 0 1 e a v HS Hi Hb Hin Ha) as Hm.
cbn [ms_mem restrict] in Hm.
assert (Hval : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (a + 0) (N.to_nat 1) v).
{ apply Hm; [exact He | change (2 ^ (8 * Z.of_N 1)) with 256; lia | lia]. }
specialize (Hval 0%nat ltac:(cbn; lia)). replace (a + 0 + Z.of_nat 0) with a in Hval by lia.
rewrite (YI04.le_byte_small v (N.to_nat 1) 0 ltac:(change (2 ^ (8 * Z.of_nat (N.to_nat 1))) with 256; lia) ltac:(cbn; lia)) in Hval.
change (8 * Z.of_nat 0) with 0 in Hval. rewrite Z.shiftr_0_r in Hval.
unfold aview. rewrite Hval. cbn [option_map]. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
rewrite (Z.mod_small v 256) by lia. reflexivity.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* the walk's Section hypotheses, with the names of a Theorem Labs lane's RULING-STMT.md section 1 *)
Hypothesis LAWS : AR_laws SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

Lemma tl_seed : forall ly S (W : world SEGS) regs mem md text sz n b,
  AR SEGS B ly S W mem md -> In (text, sz) (ablocks B ly S) -> 0 <= n -> n < sz ->
  alloc_ceiling <= spZ regs -> spZ regs + 256 <= 2 ^ 47 ->
  getr regs 25 = w64 LT_SB -> getr regs 23 = w64 n -> getr regs 18 = w64 LT_MASK -> getr regs 27 = w64 32 ->
  rdword (rdW W mem) (spZ regs + 120) = Some text -> rdW W mem (text + n) = Some b -> 0 <= b < 256 ->
  st_ok_pi SEGS VAL (tl_E regs text (text + n) b) ss_tl
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AW_T)) mem (seg_rom SEGS)))
  /\ sh_ok SEGS TLx tl_SH (tl_E regs text (text + n) b) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md text sz n b HAR Hin Hn Hnsz Hsp1 Hsp2 R25 R23 R18 R27 G120 Rb Hb.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_blocks _ _ LAWS ly S W mem md text sz HAR Hin) as (_ & Ht4096 & Htceil & Htapp & Htpres & _ & _).
pose proof (req_size_pos sz ltac:(lia)) as [Hr1 Hr2].
set (E := tl_E regs text (text + n) b).
assert (E2 : ew E 2 = getr regs 2) by (subst E; apply (tl_E_lo regs _ _ _ 2%nat 2%bv eq_refl)).
assert (E25 : ew E 25 = Z_to_bv 64 LT_SB) by (subst E; rewrite (tl_E_lo regs _ _ _ 25%nat 25%bv eq_refl); exact R25).
assert (E23 : ew E 23 = Z_to_bv 64 n) by (subst E; rewrite (tl_E_lo regs _ _ _ 23%nat 23%bv eq_refl); exact R23).
assert (E32 : ew E 32 = Z_to_bv 64 text) by (subst E; apply tl_E_32).
assert (E33 : ew E 33 = Z_to_bv 64 (text + n)) by (subst E; apply tl_E_33).
assert (E34 : ew E 34 = Z_to_bv 64 b) by (subst E; apply tl_E_34).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (U25 : bv_unsigned (ew E 25) = LT_SB) by (rewrite E25; apply unsigned_lit_small; unfold LT_SB; lia).
assert (U23 : bv_unsigned (ew E 23) = n) by (rewrite E23; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = text) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = text + n) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = b) by (rewrite E34; apply unsigned_lit_small; lia).
split.
- unfold ss_tl. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + unfold tl_sregs. apply regs_ok_rereg; [|reflexivity|].
    2: { rewrite R18. reflexivity. }
    apply regs_ok_rereg; [|reflexivity|].
    2: { rewrite R27. reflexivity. }
    subst E. unfold tl_E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    * unfold region_ok, tl_fr.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS _ _ _ 120 8 (SOff 32 0) text);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | | zside |].
      -- replace (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) by reflexivity. lia.
      -- exact (val_mem_of_rdword SEGS _ _ _ _ G120).
    * unfold region_ok, tl_tx.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U33. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable SEGS); exact (proj1 (Htpres (text + n + o) ltac:(lia)))|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS _ _ _ 0 1 (SOff 34 0) b);
        [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | | zside |].
      -- change (2 ^ (8 * Z.of_N 1)) with 256. lia.
      -- rewrite Z.add_0_r. apply tl_val_of_aval. apply tl_aval1_loc; [exact Rb | lia].
  + apply pairwise_disjoint_of_extents. unfold tl_fr, tl_tx, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, U33.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  + split; [|split].
    * cbn [tl_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U25, U32, U33, U34. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. unfold LT_SB.
      repeat match goal with |- _ /\ _ => split end; first [exact I | lia | reflexivity].
    * cbn [tl_facts f_conds conds_ok]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b].
      rewrite branch_geu_U, (U_atom _ 33 (text + n) E33 ltac:(lia)), (U_atom _ 32 text E32 ltac:(lia)).
      apply negb_true_iff, Z.ltb_ge. lia.
    * cbn [tl_facts f_alias alias_ok]. split; [|exact I].
      apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U32, U23, U33, !Z.add_0_r.
      rewrite (zcanon_small text) by lia. rewrite (zcanon_small n) by lia. reflexivity.
- unfold sh_ok, tl_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) mem E TLx 33 (text + n) 1 (text + n) 0 1).
  + exact (range_addressable_of_block SEGS B LAWS ly S W mem md text sz (text + n) 1 HAR Hin ltac:(lia) ltac:(lia)).
  + unfold U, TLx. cbn [sv_denot]. rewrite E25, Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by (unfold LT_SB; lia). reflexivity.
  + unfold U. cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
  + lia.
  + lia.
  + intros x Hx. change (Z.min 0 1) with 0 in Hx. change (Z.max 0 1) with 1 in Hx.
    unfold in_app, kLowShadowBeg in Htapp. rewrite C3 in Htapp. unfold SHADOW_OFF. lia.
Qed.

(* the two ways out of a pass, through s42's aw_ctx_kept (the registers of AW_KEEPR and every byte outside the
   text block are kept) *)
Lemma tl_exit_J : forall m cx q ly S W regs mem md k acc text copy arr regs' mem' md' T,
  AW_J_stmt B MT m -> q_m q = m -> Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
  aw_ctx B MT cx q ly S W regs mem md k acc -> aw_rec B cx q ly S W mem (aw_blocks cx q text copy arr) ->
  aw_wslots cx (rdW W mem) text copy arr ->
  ajournal SEGS B LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [] ly S W mem' md' k ->
  (forall r, In r AW_KEEPR -> getr regs' r = getr regs r) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (text <= a < text + q_L0 cx q + 1) -> rdW W mem' a = rdW W mem a) ->
  abytes_atR (rdW W mem') text T -> length T = Z.to_nat (q_L0 cx q + 1) ->
  firstn (length (q_LN cx q) + 1) T = q_LN cx q ++ [Z_to_bv 8 0] ->
  getr regs' 12 = w64 (Z.of_nat (length (q_LN cx q)) + 1) ->
  SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + AW_J)) mem' (seg_rom SEGS)) md') (lt_post B MT cx).
Proof.
intros m cx q ly S W regs mem md k acc text copy arr regs' mem' md' T HJS Hm HFRM HC HREC HWS HJ HR HK HT1 HT2 HT3 R12.
destruct (aw_ctx_kept B MT LAWS cx q ly S W regs mem md k acc text copy arr regs' mem' md' HC HREC HWS HJ HR
  ltac:(intros a Ha H1 _ _ _ _; exact (HK a Ha H1))) as (HC' & HREC' & HWS').
exact (HJS cx q ly S W regs' mem' md' k acc text copy arr Hm HFRM HC' HREC' HWS'
  (ex_intro _ T (conj HT1 (conj HT2 HT3))) R12).
Qed.
Lemma tl_exit_T : forall m j cx q ly S W regs mem md k acc text copy arr regs' mem' md',
  AW_T_stmt B MT m j -> q_m q = m -> Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
  aw_ctx B MT cx q ly S W regs mem md k acc -> aw_rec B cx q ly S W mem (aw_blocks cx q text copy arr) ->
  aw_wslots cx (rdW W mem) text copy arr ->
  ajournal SEGS B LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [] ly S W mem' md' k ->
  (forall r, In r AW_KEEPR -> getr regs' r = getr regs r) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (text <= a < text + q_L0 cx q + 1) -> rdW W mem' a = rdW W mem a) ->
  (1 <= j <= length (q_U cx q))%nat ->
  Verbs.trim (q_U cx q) = Verbs.trim (firstn j (q_U cx q)) ->
  abytes_atR (rdW W mem') text (SlotWordsRun.tz (q_U cx q) j) ->
  getr regs' 23 = w64 (Z.of_nat j - 1) ->
  SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + AW_T)) mem' (seg_rom SEGS)) md') (lt_post B MT cx).
Proof.
intros m j cx q ly S W regs mem md k acc text copy arr regs' mem' md' HIH Hm HFRM HC HREC HWS HJ HR HK Hj HT Htz R23.
destruct (aw_ctx_kept B MT LAWS cx q ly S W regs mem md k acc text copy arr regs' mem' md' HC HREC HWS HJ HR
  ltac:(intros a Ha H1 _ _ _ _; exact (HK a Ha H1))) as (HC' & HREC' & HWS').
exact (HIH cx q ly S W regs' mem' md' k acc text copy arr Hm HFRM HC' HREC' HWS' Hj HT Htz R23).
Qed.

(* the write window of a pass: the byte text + j (the text region's), in the block text made since the entry; the
   frame region has no write window *)
Ltac tl_awr E33u HtIn Htnot :=
  lazymatch goal with |- awr_ok ?sg ?bb ?E0 ?rs ?stk ?sp0 ?fp ?b0 ?bc ?fr ?ly0 ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb E0 rs' stk sp0 fp b0 bc fr ly0 own) end;
  eapply awr_ok_cons_gen; [reflexivity | reflexivity | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; lia | ];
  eapply awr_ok_cons_gen; [reflexivity | cbn [ew ewset Nat.eqb]; exact E33u | | apply awr_ok_nil];
  intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha;
  right; right; left; eexists _, _; split; [exact HtIn | split; [exact Htnot | lia]].
(* the memory a run left: the byte a0 is the only one it may change *)
Ltac tl_keep W mem KP KN a0 E33u :=
  lazymatch goal with Hfr : frame_of _ _ (mrestrict _ _) (mrestrict _ ?m2) |- _ =>
  assert (KN : forall a, 0 <= a < 2 ^ 64 -> a <> a0 -> rdW W m2 a = rdW W mem a)
    by (intros a Ha Hna; rewrite (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => a = a0) Hfr);
        [ exact (KP a Ha Hna)
        | intros bb wlo whi a' Hin Hrr; vm_compute in Hin;
          destruct Hin as [Hq0 | [Hq0 | []]]; injection Hq0 as <- <- <-; cbn [base_val ew ewset Nat.eqb] in Hrr;
          [lia | rewrite E33u in Hrr; lia]
        | exact Ha | exact Hna ])
  end.
Ltac tl_mdv name :=
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (name := d) in *; clearbody name end.
(* the registers of AW_KEEPR at the end of a run: 18 and 27 are the seed's literals, the rest its atoms *)
Ltac tl_kept_regs HS regs ext HAE0 R18 R27 HKall :=
  let P18 := fresh "P18" in let P27 := fresh "P27" in let HAE4 := fresh "HAE" in let HKB := fresh "HKB" in
  prreg HS (18%bv : bv 5) P18; prreg HS (27%bv : bv 5) P27;
  lazymatch type of HS with st_ok_pi _ _ ?E4 _ _ =>
    assert (HAE4 : env_agree 32 (Ereg regs ext) E4)
      by (let HA1 := fresh "HA1" in let HA2 := fresh "HA2" in pose proof HAE0 as [HA1 HA2]; split;
          [ intros n Hn32; cbn [ew ewset];
            repeat match goal with |- context [Nat.eqb ?a ?b] => destruct (Nat.eqb_spec a b); [lia|] end;
            exact (HA1 n Hn32)
          | cbn [ed ewset]; exact HA2 ])
  end;
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs ext [2; 3; 4; 8; 9; 19; 20; 21; 22; 25; 26]%bv HS HAE4
    ltac:(vm_compute; reflexivity)) as HKB;
  cbn [ms_regs restrict] in HKB;
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?ms) =>
  assert (HKall : forall r, In r AW_KEEPR -> getr (ms_regs ms) r = getr regs r)
    by (intros r Hr0; cbn [AW_KEEPR In] in Hr0;
        repeat (destruct Hr0 as [<- | Hr0];
          [ first [ rewrite P18, R18; reflexivity | rewrite P27, R27; reflexivity
                  | apply HKB; cbn [In]; repeat (first [left; reflexivity | right]) ] |]);
        destruct Hr0)
  end;
  clear P18 P27 HAE4 HKB.

(* one pass: from 0x86800 with j + 1 bytes left to 0x86800 with j left, or out to 0x868bc *)
Lemma tl_step : forall m j, AW_J_stmt B MT m -> AW_T_stmt B MT m j -> AW_T_stmt B MT m (S j).
Proof.
intros m j HJS HIH cx q ly St W regs mem md k acc text copy arr Hm HFRM HC HREC HWS Hj HT Htz R23.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : LTOI_STK = 32768) by reflexivity.
pose proof HC as ((HB0 & ((HJ & Hsp & R3 & R4 & HSV) & HSL & R8 & R9 & R18 & R25 & R26 & R27 & Hmq) &
  (Hr & R19 & R20 & R21 & R22 & Hst & Hho & Hh)) & Hbud).
pose proof HB0 as (HPRE & _).
pose proof HPRE as (_ & _ & _ & Hgp & Htp & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
rewrite WS in Hslo.
assert (Hs0 : alloc_ceiling + 32768 <= x_sp0 cx <= 2 ^ 47) by (unfold x_sp0; lia).
assert (Hs1 : x_sp1 cx = x_sp0 cx - 256) by (unfold x_sp1, x_sp0, LT_FRAME; lia).
pose proof (proj1 HJ) as HAR.
pose proof HREC as (HRR & Hspill & Hcalls & Hquit & Hq & HPERM).
pose proof (q_L0_U cx q) as HL0U.
(* the text block: live, made since the entry *)
assert (HtB : In (text, q_L0 cx q + 1) (aw_blocks cx q text copy arr)) by (rewrite aw_blocks_eq; left; reflexivity).
assert (HtIn : In (text, q_L0 cx q + 1) (ablocks B ly St))
  by exact (Permutation_in _ (Permutation_sym HPERM) (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror HtB))))).
pose proof (lt_ablocks_NoDup B LAWS ly St W mem md HAR) as HND.
pose proof (Permutation_NoDup HPERM HND) as HND2.
assert (Htnot : ~ In (text, q_L0 cx q + 1) (x_bl0 B cx)).
{ intros Hin. exact (wc_nodup_app_loc _ _ _ (wc_nodup_app_r_loc _ _ HND2) Hin HtB). }
destruct (al_blocks _ _ LAWS ly St W mem md text (q_L0 cx q + 1) HAR HtIn) as (_ & Ht4096 & Htceil & _ & _ & _ & _).
pose proof (req_size_pos (q_L0 cx q + 1) ltac:(lia)) as [Hrq1 Hrq2].
(* the byte of this pass *)
assert (HjU : (S j <= length (q_U cx q))%nat) by lia.
destruct (nth_error (q_U cx q) j) as [x|] eqn:Ex; [|apply nth_error_None in Ex; lia].
pose proof (bv_unsigned_in_range 8 x) as Rx. change (bv_modulus 8) with 256 in Rx.
remember (bv_unsigned x) as b eqn:Eb.
assert (Hlen : length (SlotWordsRun.tz (q_U cx q) (S j)) = S (length (q_U cx q))) by (apply SlotWordsRun.tz_len; lia).
assert (Hrdb : rdW W mem (text + Z.of_nat j) = Some b).
{ rewrite (Htz j ltac:(rewrite Hlen; lia)). rewrite Eb. f_equal. f_equal. apply nth_error_nth.
  rewrite SlotWordsRun.tz_nth_lt by lia. exact Ex. }
assert (G120 : rdword (rdW W mem) (spZ regs + 120) = Some text).
{ pose proof HWS as (HW0 & _ & _). rewrite Hsp. unfold LT_W in HW0. exact HW0. }
assert (R23' : getr regs 23 = w64 (Z.of_nat j)) by (rewrite R23; f_equal; lia).
(* the seed *)
destruct (tl_seed ly St W regs mem md text (q_L0 cx q + 1) (Z.of_nat j) b HAR HtIn ltac:(lia) ltac:(lia)
  ltac:(rewrite Hsp; lia) ltac:(rewrite Hsp; lia) R25 R23' R18 R27 G120 Hrdb ltac:(lia)) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (tl_E regs text (text + Z.of_nat j) b)) by (unfold tl_E; apply Eimg_env).
pose proof (tl_E_agree regs text (text + Z.of_nat j) b) as HAE0.
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (tl_E regs text (text + Z.of_nat j) b) n = getr regs rr)
  by (intros n rr Hrr; exact (tl_E_lo regs _ _ _ n rr Hrr)).
assert (E33u : bv_unsigned (ew (tl_E regs text (text + Z.of_nat j) b) 33) = text + Z.of_nat j)
  by (rewrite tl_E_33; apply unsigned_lit_small; lia).
pose proof (tl_E_34 regs text (text + Z.of_nat j) b) as E34.
assert (E23 : ew (tl_E regs text (text + Z.of_nat j) b) 23 = Z_to_bv 64 (Z.of_nat j))
  by (rewrite (EEo 23%nat 23%bv eq_refl); exact R23').
assert (E8u : bv_unsigned (ew (tl_E regs text (text + Z.of_nat j) b) 8) = 2 ^ 64 - 1)
  by (rewrite (EEo 8%nat 8%bv eq_refl), R8; reflexivity).
remember (tl_E regs text (text + Z.of_nat j) b) as E0 eqn:HE0. clear HE0.
assert (KK0 : forall a, 0 <= a < 2 ^ 64 -> a <> text + Z.of_nat j -> rdW W mem a = rdW W mem a) by (intros; reflexivity).
(* the model of the pass *)
assert (Hbt : text + Z.of_nat (length (q_U cx q)) + 1 <= 2 ^ 64) by lia.
(* 0x86800 .. 0x86834: text reloaded, a0 = text + s7, UBSan's three tests, the load check, lbu, `bltu s11,a2` *)
paj_run_tok RUN HS HJ SHOK TLspan.
{ tl_awr E33u HtIn Htnot. }
tl_mdv mdv1. tl_keep W mem KK0 KEEP1 (text + Z.of_nat j) E33u. clear HF HFr HG KK0. rename ms into ms1.
psrr_branch_tok RUN BR HS SHOK TLspan.
- (* the byte is above 32: not trailing; the line is the first j + 1 bytes *)
  assert (Hgt : 32 < b).
  { rewrite branch_ltu_U, U_lit, (U_atom _ 34 b) in Hc by first [lia | cbn [ew ewset Nat.eqb]; exact E34].
    apply Z.ltb_lt in Hc. exact Hc. }
  assert (Hnt : Verbs.is_trail x = false)
    by (rewrite SlotWords.sw_is_trail_z, <- Eb; apply SlotWords.sw_trail_big; exact Hgt).
  assert (ELN : q_LN cx q = firstn (S j) (q_U cx q))
    by (change (q_LN cx q) with (Verbs.trim (q_U cx q)); rewrite HT; exact (SlotWordsRun.sw_trim_line _ j x Ex Hnt)).
  (* 0x86834 .. 0x868b8: a2 = s7 + 2, on to 0x868bc *)
  paj_run_to_tok RUNTO HS HJ SHOK TLspan 0x38c.
  { tl_awr E33u HtIn Htnot. }
  tl_mdv mdv2. tl_keep W mem KEEP1 KEEP (text + Z.of_nat j) E33u. clear HF HFr HG KEEP1.
  lazymatch type of HS with st_ok_pi _ _ ?E2 ?ss2 _ =>
    let rgl := eval vm_compute in (nth_error (ss_mem ss2) 1) in
    lazymatch rgl with Some ?rg =>
      assert (Rst : rdW W (ms_mem ms) (text + Z.of_nat j) = Some b)
        by (apply (tl_chunk_byte W E2 (abs_ss VAL ss2) ms rg (SOff 34 0) b); [exact HS | reflexivity | reflexivity
          | cbn [In YP09.r_chunks]; left; reflexivity
          | cbn [ew ewset Nat.eqb]; exact E33u
          | cbn [sv_denot ew ewset Nat.eqb]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia])
    end end.
  pmkst HS.
  prreg HS (12%bv : bv 5) P12.
  tl_kept_regs HS regs [Z_to_bv 64 text; Z_to_bv 64 (text + Z.of_nat j); Z_to_bv 64 b] HAE0 R18 R27 HKall.
  assert (KA : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms) a = rdW W mem a).
  { intros a Ha. destruct (Z.eq_dec a (text + Z.of_nat j)) as [->|Hne]; [rewrite Rst, Hrdb; reflexivity | exact (KEEP a Ha Hne)]. }
  apply (tl_exit_J m cx q ly St W regs mem md k acc text copy arr (ms_regs ms) (ms_mem ms) mdv2
    (SlotWordsRun.tz (q_U cx q) (S j)) HJS Hm HFRM HC HREC HWS HJ HKall).
  + intros a Ha _. exact (KA a Ha).
  + intros i Hi. rewrite KA by (rewrite Hlen in Hi; lia). exact (Htz i Hi).
  + rewrite Hlen, HL0U. lia.
  + rewrite ELN, firstn_length_le by lia. apply SlotWordsRun.tz_firstn. lia.
  + rewrite P12, E23, unsigned_lit_small by lia. rewrite ELN, firstn_length_le by lia. unfold w64. f_equal. lia.
- (* the byte is 32 or below: its bit of the mask *)
  assert (Hle : b <= 32).
  { rewrite branch_ltu_U, U_lit, (U_atom _ 34 b) in Hc by first [lia | cbn [ew ewset Nat.eqb]; exact E34].
    apply Z.ltb_ge in Hc. exact Hc. }
  clear Hc.
  (* 0x86834 .. 0x86840: srl, andi, `beqz a2` *)
  paj_run_tok RUN HS HJ SHOK TLspan.
  { tl_awr E33u HtIn Htnot. }
  tl_mdv mdv2. tl_keep W mem KEEP1 KEEP2 (text + Z.of_nat j) E33u. clear HF HFr HG KEEP1. rename ms into ms2.
  psrr_branch_tok RUN BR HS SHOK TLspan.
  + (* the bit is 0: not trailing *)
    assert (Hnt : Verbs.is_trail x = false).
    { rewrite branch_eq_U, (tl_mask_U _ b), U_lit in Hc by first [lia | cbn [ew ewset Nat.eqb]; exact E34].
      rewrite SlotWords.sw_is_trail_z, <- Eb. destruct (SlotWords.sw_trail_z b); cbn in Hc; [discriminate Hc | reflexivity]. }
    assert (ELN : q_LN cx q = firstn (S j) (q_U cx q))
      by (change (q_LN cx q) with (Verbs.trim (q_U cx q)); rewrite HT; exact (SlotWordsRun.sw_trim_line _ j x Ex Hnt)).
    paj_run_to_tok RUNTO HS HJ SHOK TLspan 0x38c.
    { tl_awr E33u HtIn Htnot. }
    tl_mdv mdv3. tl_keep W mem KEEP2 KEEP (text + Z.of_nat j) E33u. clear HF HFr HG KEEP2.
    lazymatch type of HS with st_ok_pi _ _ ?E2 ?ss2 _ =>
      let rgl := eval vm_compute in (nth_error (ss_mem ss2) 1) in
      lazymatch rgl with Some ?rg =>
        assert (Rst : rdW W (ms_mem ms) (text + Z.of_nat j) = Some b)
          by (apply (tl_chunk_byte W E2 (abs_ss VAL ss2) ms rg (SOff 34 0) b); [exact HS | reflexivity | reflexivity
            | cbn [In YP09.r_chunks]; left; reflexivity
            | cbn [ew ewset Nat.eqb]; exact E33u
            | cbn [sv_denot ew ewset Nat.eqb]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia])
      end end.
    pmkst HS.
    prreg HS (12%bv : bv 5) P12.
    tl_kept_regs HS regs [Z_to_bv 64 text; Z_to_bv 64 (text + Z.of_nat j); Z_to_bv 64 b] HAE0 R18 R27 HKall.
    assert (KA : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms) a = rdW W mem a).
    { intros a Ha. destruct (Z.eq_dec a (text + Z.of_nat j)) as [->|Hne]; [rewrite Rst, Hrdb; reflexivity | exact (KEEP a Ha Hne)]. }
    apply (tl_exit_J m cx q ly St W regs mem md k acc text copy arr (ms_regs ms) (ms_mem ms) mdv3
      (SlotWordsRun.tz (q_U cx q) (S j)) HJS Hm HFRM HC HREC HWS HJ HKall).
    * intros a Ha _. exact (KA a Ha).
    * intros i Hi. rewrite KA by (rewrite Hlen in Hi; lia). exact (Htz i Hi).
    * rewrite Hlen, HL0U. lia.
    * rewrite ELN, firstn_length_le by lia. apply SlotWordsRun.tz_firstn. lia.
    * rewrite P12, E23, unsigned_lit_small by lia. rewrite ELN, firstn_length_le by lia. unfold w64. f_equal. lia.
  + (* the bit is 1: a trailing byte; zero it and go down *)
    assert (Htr : Verbs.is_trail x = true).
    { rewrite branch_eq_U, (tl_mask_U _ b), U_lit in Hc by first [lia | cbn [ew ewset Nat.eqb]; exact E34].
      rewrite SlotWords.sw_is_trail_z, <- Eb. destruct (SlotWords.sw_trail_z b); cbn in Hc; [reflexivity | discriminate Hc]. }
    assert (HT' : Verbs.trim (q_U cx q) = Verbs.trim (firstn j (q_U cx q)))
      by (rewrite HT; exact (SlotWordsRun.sw_trim_step _ j x Ex Htr)).
    clear Hc.
    (* 0x86844 .. 0x86858: UBSan's null test of a0, the store check (the shadow entry), s7 -= 1, the store, `bne` *)
    paj_run_tok RUN HS HJ SHOK TLspan.
    { tl_awr E33u HtIn Htnot. }
    tl_mdv mdv3. tl_keep W mem KEEP2 KEEP3 (text + Z.of_nat j) E33u. clear HF HFr HG KEEP2. rename ms into ms3.
    psrr_branch_tok RUN BR HS SHOK TLspan.
    * (* j <> 0: the next pass *)
      assert (Hj1 : (1 <= j)%nat).
      { rewrite (tl_ne_U _ (Z.of_nat j)) in Hc by first [lia | cbn [ew ewset Nat.eqb]; exact E23 | cbn [ew ewset Nat.eqb]; exact E8u].
        apply negb_true_iff, Z.eqb_neq in Hc. lia. }
      paj_run_to_tok RUNTO HS HJ SHOK TLspan 0x2d0.
      { tl_awr E33u HtIn Htnot. }
      tl_mdv mdv4. tl_keep W mem KEEP3 KEEP (text + Z.of_nat j) E33u. clear HF HFr HG KEEP3.
      lazymatch type of HS with st_ok_pi _ _ ?E2 ?ss2 _ =>
        let rgl := eval vm_compute in (nth_error (ss_mem ss2) 1) in
        lazymatch rgl with Some ?rg =>
          assert (Rst : rdW W (ms_mem ms) (text + Z.of_nat j) = Some 0)
            by (apply (tl_chunk_byte W E2 (abs_ss VAL ss2) ms rg (SLit 0) 0); [exact HS | reflexivity | reflexivity
              | cbn [In YP09.r_chunks]; left; reflexivity
              | cbn [ew ewset Nat.eqb]; exact E33u
              | reflexivity | lia])
        end end.
      pmkst HS.
      prreg HS (23%bv : bv 5) P23.
      tl_kept_regs HS regs [Z_to_bv 64 text; Z_to_bv 64 (text + Z.of_nat j); Z_to_bv 64 b] HAE0 R18 R27 HKall.
      apply (tl_exit_T m j cx q ly St W regs mem md k acc text copy arr (ms_regs ms) (ms_mem ms) mdv4
        HIH Hm HFRM HC HREC HWS HJ HKall).
      -- intros a Ha Hn. apply KEEP; [exact Ha | lia].
      -- lia.
      -- exact HT'.
      -- exact (tl_tz_store (rdW W mem) _ text (q_U cx q) j HjU ltac:(lia) Hbt Htz KEEP Rst).
      -- rewrite P23, E23, unsigned_lit_small by lia. unfold w64; f_equal; lia.
    * (* j = 0: every byte was trailing; the line is empty *)
      assert (Hj0 : j = 0%nat).
      { rewrite (tl_ne_U _ (Z.of_nat j)) in Hc by first [lia | cbn [ew ewset Nat.eqb]; exact E23 | cbn [ew ewset Nat.eqb]; exact E8u].
        apply negb_false_iff, Z.eqb_eq in Hc. lia. }
      assert (ELN : q_LN cx q = [])
        by (change (q_LN cx q) with (Verbs.trim (q_U cx q)); rewrite HT', Hj0; reflexivity).
      (* 0x8685c .. 0x868b8: a2 = 0 + 1, on to 0x868bc *)
      paj_run_to_tok RUNTO HS HJ SHOK TLspan 0x38c.
      { tl_awr E33u HtIn Htnot. }
      tl_mdv mdv4. tl_keep W mem KEEP3 KEEP (text + Z.of_nat j) E33u. clear HF HFr HG KEEP3.
      lazymatch type of HS with st_ok_pi _ _ ?E2 ?ss2 _ =>
        let rgl := eval vm_compute in (nth_error (ss_mem ss2) 1) in
        lazymatch rgl with Some ?rg =>
          assert (Rst : rdW W (ms_mem ms) (text + Z.of_nat j) = Some 0)
            by (apply (tl_chunk_byte W E2 (abs_ss VAL ss2) ms rg (SLit 0) 0); [exact HS | reflexivity | reflexivity
              | cbn [In YP09.r_chunks]; left; reflexivity
              | cbn [ew ewset Nat.eqb]; exact E33u
              | reflexivity | lia])
        end end.
      pmkst HS.
      prreg HS (12%bv : bv 5) P12.
      tl_kept_regs HS regs [Z_to_bv 64 text; Z_to_bv 64 (text + Z.of_nat j); Z_to_bv 64 b] HAE0 R18 R27 HKall.
      pose proof (tl_tz_store (rdW W mem) _ text (q_U cx q) j HjU ltac:(lia) Hbt Htz KEEP Rst) as Htz0.
      subst j.
      apply (tl_exit_J m cx q ly St W regs mem md k acc text copy arr (ms_regs ms) (ms_mem ms) mdv4
        (SlotWordsRun.tz (q_U cx q) 0) HJS Hm HFRM HC HREC HWS HJ HKall).
      -- intros a Ha Hn. apply KEEP; [exact Ha | lia].
      -- exact Htz0.
      -- rewrite SlotWordsRun.tz_len, HL0U by lia. lia.
      -- rewrite ELN. apply (SlotWordsRun.tz_firstn _ 0). lia.
      -- rewrite P12, ELN. reflexivity.
Qed.

(* the trim loop: from its head with any j, by induction on j (the base j = 0 is outside the loop's premise) *)
Lemma aw_seg_Tloop : forall m, AW_J_stmt B MT m -> forall j, AW_T_stmt B MT m j.
Proof.
intros m HJS j. induction j as [|j IH].
- intros cx q ly S W regs mem md k acc text copy arr _ _ _ _ _ Hj. exfalso. lia.
- exact (tl_step m j HJS IH).
Qed.

End e.
End f.
End d.
