(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFl3.v:106-108
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:383-389, 448-454, 493-498, 501-509 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:625-631 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:208-214, 227-233 [Apache-2.0 OR MIT], for libreac/fuzz_identity's ASan
   build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_name_seg10.v, with its module paths and module names changed; 2634 of its 2686 lines of code are new or changed and 608 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSH_parse_value.v; 148 of its 216 lines of code are new or changed and 2618 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_frame3.v, with its module paths and module names changed; 1118 of its 1151 lines of code are new or changed and 183 lines of the source are left out. *)
(* past_nul B 0x82894 (fuzz_state.c) over fs.asan-ubsan: the ASan walk proving lib/B/FSH_Fn_cno.v's past_nul_spec
   (CTX-free, S0 f32db4da382) at fs.asan-ubsan's image (lib/B tfibsegs), build B's sink head FSH_Base.fsB_sink_head
   passed explicitly.
   MEASURED (capstone over the pinned fs.asan-ubsan, sha256 5ac5ce0954f8..., 0x82894 .. 0x829f0): 87 instructions,
   348 bytes, no compressed instruction; real 64-byte frame (ra, s0 .. s6 saved at sp + 56 .. 0), plain T entry
   fss0T / fsw_entryT, no re-align. The calls (the call map): __wrap_malloc 0x828d4 (n + 18), __asan_memcpy 0x828f0
   (t, d, n; skipped when n = 0), __asan_memset 0x82930 (t + n + 1, 0, 16); __asan_handle_no_return 0x829ac and abort
   0x829b0 on the NULL arm; __asan_report_store1 0x829c4 / 0x829d0 / 0x829e0 / 0x829ec on the four inline checks.
   The walk:
   - the entry run to the HARNESS allocator `jal __wrap_malloc` 0x828d4 with a0 = n + 18; the call is ALLOC's
     lib/B/FSW_malloc_free.fsw_aj_malloc04U (S0 form: its C5 premise `In (call_trace ..) (as_universe B) \/
     st_nev S < EV_MAX` is closed inside by the second disjunct, from st_nev S < EV_MAX, which the spec's budget
     st_nev S + EV_past_nul <= EV_MAX gives, EV_past_nul = 1); the resume is FSW_rres.fsw_resume_after_rtU_args_chunks;
   - `beqz a0` 0x828d8 (-> 0x829ac __asan_handle_no_return; abort) is untaken: t >= 4096;
   - `beqz s3` 0x828e0 splits n = 0 (straight to the join 0x828f4) from n > 0 (`jal __asan_memcpy` 0x828f0 copies the
     n source bytes, FSW_K.fsw_intrin_atU; the spec's source-block premise keeps them across the malloc and makes the
     copy's ranges disjoint); pn_post takes both at the join 0x828f4;
   - pn_post: UBSan guard U1 `bltu s5, s3` 0x828f8 (s5 = ~t) is untaken (t + n < 2 ^ 47); s2 := t + n is re-seated on a
     fresh atom (FSW_K.fsw_reseat_atom), so FSW_K's token run takes the inline check of the store t[n] := 0
     (0x82900 .. 0x8290c; the shadow entry covers [t + n, t + n + 8), inside the block), the store 0x82914 and the UBSan
     guard U2 `beq s2, -1` 0x82918 (decided by the re-seated atom's fact t + n <= 2 ^ 47 - 8), up to the memset call;
   - pn_tail: `jal __asan_memset` 0x82930 zeroes [t + n + 1, t + n + 17); UBSan guard U3 `bltu s5, s6` 0x82934
     (s6 = n + 17) is untaken; a0 := t + n + 17 is re-seated; the token run takes the three inline checks (0x82940 ..
     0x82948, 0x82950 .. 0x8295c, 0x82964 .. 0x82974) and the stores t[n + 17] := 0, t[n + 1] := c, t[n + 2] := 'A' to
     the `ret` 0x829a8 with no open shadow obligation;
   - the return: FSW_ret.fsw_retU to apost_baseU with U' = U, k = EV_past_nul = 1, the block appended, pn_copy db c at
     t, the alloc.c statics unchanged (journal image clause, fs_img_facts' FS_PSTAT_FP conjunct), the heads U still in
     their (old) blocks.
   R2, the report-site checklist rows (a Theorem Labs lane's reloc-check/report-sites-B.tsv, fn = past_nul), each refuted:
   - 0x829b4 unimp (deciding 0x828f8 bltu, 0x82918 beq, 0x82934 bltu): pn_post's U1 branch is closed by exfalso from
     pn_U_not (s5 = 2 ^ 64 - 1 - t) and t + n + 18 <= alloc_ceiling < 2 ^ 47, n <= 2 ^ 22; U2 is never stopped at: the
     token run decides it from the re-seated atom's fact; pn_tail's U3 branch is closed by exfalso the same way as U1.
     The `after call at 0x829b0` entry is the abort call of the NULL arm, closed by exfalso (t >= 4096).
   - 0x829c4 __asan_report_store1 (0x8290c bne): the token run reads shadow 0 (shadow entry [t + n, t + n + 8) range
     addressable on the block), so the bne is untaken; the run never reaches 0x829b8.
   - 0x829d0 (0x82948 bne), 0x829e0 (0x8295c bne), 0x829ec (0x82974 bne): the token run's slow-path blocks
     (0x829c8, 0x829d4, 0x829e4) are taken back to the store under the shadow entries [t + n + 17, + 1), [t + n + 1, + 1)
     and [t + n + 1, t + n + 3), each range addressable on the block (pn_ra_raw); no report call is reached and no
     obligation is left (sh_obls = []).
   Callee contracts taken as Section hypotheses: the FsRt fields fr_malloc, fr_memcpy, fr_memset (lib/B/FSH_Rt.v), the
   image facts fs_img_facts, api_env, model_laws and the two shadow-base cells of B. No CTX, no trace row.
   Control flow templates (text only, no byte offset copied): lib/A/FSW_past_nul.v (a working branch
   c535009186d) and the bespoke a working branch e3747952ca00 lib/B/Prog/past_nul.v. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSPstat FSW_K FSW_ret FSW_rres FSW_malloc_free FSH_Fn_cno FSW_past_nul_tbl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Ltac pn_csv := unfold acallee_saved;
  lazymatch goal with |- context [bv_unsigned ?q] => let z := eval vm_compute in (bv_unsigned q) in change (bv_unsigned q) with z end; lia.

Ltac pn_sr HS q := rewrite (st_ok_restrict_reg tfibsegs _ _ _ _ q HS);
  lazymatch goal with |- context [sr_get ?l q] => let v := eval vm_compute in (sr_get l q) in change (sr_get l q) with v end.

(* the machine value of register q after a run, from the symbolic state and the env's atom equations in context *)
Ltac pn_val HS q E :=
  unfold w64; pn_sr HS q; rewrite denot_lit_U; f_equal;
  rewrite ?U_SAlu; cbn [zalu_raw];
  repeat match goal with
   | H : ew E ?k = Z_to_bv 64 ?v |- context [YP0e.U E (SOff ?k ?c)] =>
       rewrite (U_atom_off E k v c H) by (unfold SHADOW_OFF in *; lia)
   end;
  rewrite ?U_lit by lia;
  try (rewrite zcanon_id; [|unfold M64, SHADOW_OFF in *; lia]); unfold SHADOW_OFF in *; lia.

(* the callee-saved registers no walk step touches (gp, tp, s7 .. s11), read on a run's state *)
Ltac pn_rcsv HS VQ :=
  let q := fresh "q" in let Hq := fresh "Hq" in
  intros q Hq;
  assert (Hq' : q = 3 \/ q = 4 \/ q = 23 \/ q = 24 \/ q = 25 \/ q = 26 \/ q = 27) by lia;
  destruct Hq' as [->|[->|[->|[->|[->|[->| ->]]]]]];
  lazymatch goal with |- getr _ ?r = _ => pn_sr HS r end; rewrite fsw_SOff0;
  lazymatch goal with |- ew _ ?k = _ => rewrite (VQ k ltac:(lia)); reflexivity end.

(* the side goals of the write-window steps (the awr_ok_cons lemmas), each by its shape (kit rule R1) *)
Ltac pn_awr_side Esp :=
  lazymatch goal with
  | |- YP09.r_base _ = Some _ => reflexivity
  | |- bv_unsigned _ = _ => rewrite Esp; lia
  | |- (_ <= _)%Z => cbn [YP09.r_wlo YP09.r_whi fstk_ret fstk]; lia
  | |- (_ < _)%Z => cbn [YP09.r_wlo YP09.r_whi fstk_ret fstk]; lia
  | |- awr_ok _ _ _ _ _ _ _ _ _ _ _ _ => idtac
  end.

(* ---- pure facts ---- *)
(* `not` on a 64-bit value *)
Lemma pn_lxor_ones : forall x, 0 <= x < 2 ^ 64 -> Z.lxor x (2 ^ 64 - 1) = 2 ^ 64 - 1 - x.
Proof.
intros x Hx. change (2 ^ 64 - 1) with (Z.ones 64).
assert (HL : Z.land (Z.lxor x (Z.ones 64)) x = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.lxor_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i 64) as [Hl|Hh].
  - rewrite Z.ones_spec_low by lia. destruct (Z.testbit x i); reflexivity.
  - assert (Hb : Z.testbit x i = false).
    { rewrite <- (Z.mod_small x (2 ^ 64)) by lia. apply Z.mod_pow2_bits_high. lia. }
    rewrite Hb. apply andb_false_r. }
pose proof (Z.add_nocarry_lxor _ _ HL) as Hs.
rewrite (Z.lxor_comm (Z.lxor x (Z.ones 64)) x), <- Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_l in Hs.
lia.
Qed.
Lemma pn_U_not : forall E k v, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  YP0e.U E (SAlu ALU_XOR (SOff k 0) (SLit (-1))) = 2 ^ 64 - 1 - v.
Proof.
intros E k v H Hv. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E k v H Hv), U_SLit.
change (zcanon (-1)) with (2 ^ 64 - 1). rewrite pn_lxor_ones by exact Hv. apply zcanon_id. unfold M64. lia.
Qed.
Lemma pn_U_add : forall E k1 k2 v1 v2, ew E k1 = Z_to_bv 64 v1 -> ew E k2 = Z_to_bv 64 v2 ->
  0 <= v1 -> 0 <= v2 -> v1 + v2 < 2 ^ 64 -> YP0e.U E (SAlu ALU_ADD (SOff k1 0) (SOff k2 0)) = v1 + v2.
Proof.
intros E k1 k2 v1 v2 H1 H2 P1 P2 Hs. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E k1 v1 H1 ltac:(lia)), (U_atom E k2 v2 H2 ltac:(lia)). apply zcanon_id. unfold M64. lia.
Qed.

(* fs.asan-ubsan's image hull is loaded bytes (its four PT_LOADs are 0x10000 .. 0x5fd000 with no gap, MEASURED by
   vm_compute below). lib/B/YD1y.v in_img_hull states it too, but YD1y's Require cone loads lib/B/YD2j.v (RELOC-B's
   region pair), which this walk's cone avoids. *)
Lemma pn_img : forall a, 0x10000 <= a < 0x5fd000 -> in_img tfibsegs a.
Proof.
intros a Ha.
assert (Hs : map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs =
  [(65536, 131072); (196608, 454656); (651264, 8192); (659456, 5619712)]) by (vm_compute; reflexivity).
unfold in_img. remember tfibsegs as L eqn:EL. clear EL.
destruct L as [|s0 [|s1 [|s2 [|s3 [|s4 L]]]]]; cbn [map] in Hs; try discriminate.
injection Hs as E0 E1 E2 E3.
destruct (Z_lt_le_dec a 0x30000); [exists s0; cbn [In]; split; [tauto | lia]|].
destruct (Z_lt_le_dec a 0x9f000); [exists s1; cbn [In]; split; [tauto | lia]|].
destruct (Z_lt_le_dec a 0xa1000); [exists s2; cbn [In]; split; [tauto | lia]|].
exists s3; cbn [In]; split; [tauto | lia].
Qed.

Lemma pn_copy_len : forall db c, length (pn_copy db c) = (length db + 18)%nat.
Proof. intros db c. unfold pn_copy. rewrite !length_app, repeat_length. reflexivity. Qed.
Lemma pn_copy_head : forall db c j, (j < length db)%nat -> nth j (pn_copy db c) 0 = nth j db 0.
Proof. intros db c j Hj. unfold pn_copy. apply app_nth1. exact Hj. Qed.
Lemma pn_copy_tail : forall db c k, (k < 18)%nat ->
  nth (length db + k) (pn_copy db c) 0 = nth k ([0; c mod 256; 65] ++ repeat 0 15) 0.
Proof. intros db c k Hk. unfold pn_copy. rewrite app_nth2 by lia. f_equal. lia. Qed.
Lemma pn_copy_bytes : forall db c, Forall (fun z => 0 <= z < 256) db -> Forall (fun z => 0 <= z < 256) (pn_copy db c).
Proof.
intros db c Hdb. unfold pn_copy. apply Forall_app. split; [exact Hdb|].
apply Forall_app. split.
- repeat constructor; try lia; apply Z.mod_pos_bound; lia.
- apply Forall_forall. intros x Hx. apply repeat_spec in Hx. lia.
Qed.

Lemma pn_garr8 : forall H m base l, Forall (fun z => 0 <= z < 256) l ->
  (forall j, (j < length l)%nat -> aview tfibsegs H m (base + Z.of_nat j) = Some (nth j l 0)) ->
  garr8 tfibsegs (mrestrict H m) base l.
Proof.
intros H m base l Hb Hv j Hj.
assert (Bj : 0 <= nth j l 0 < 256) by (exact (proj1 (Forall_nth _ l) Hb j 0 Hj)).
split; [|exact Bj]. intros k Hk. assert (k = 0%nat) as -> by lia.
destruct (aview_byte tfibsegs H m _ _ (Hv j Hj)) as (b & Hm & Ev & _).
rewrite Z.add_0_r. rewrite Hm. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned.
unfold YO0f.le_byte. cbn [Z.of_nat]. rewrite Z.mul_0_r, Z.shiftr_0_r. change (2 ^ (8 * 1)) with 256.
rewrite !Z.mod_small by lia. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_small by lia. lia.
Qed.
Lemma pn_aview_of_garr8 : forall H m base l j, garr8 tfibsegs (mrestrict H m) base l -> (j < length l)%nat ->
  aview tfibsegs H m (base + Z.of_nat j) = Some (nth j l 0).
Proof.
intros H m base l j Hg Hj. destruct (Hg j Hj) as [Hv Bj]. specialize (Hv 0%nat ltac:(lia)).
rewrite Z.add_0_r in Hv. unfold aview. rewrite Hv. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold YO0f.le_byte. cbn [Z.of_nat]. rewrite Z.mul_0_r, Z.shiftr_0_r. change (2 ^ (8 * 1)) with 256.
rewrite !Z.mod_small by lia. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. lia.
Qed.
Lemma pn_chunk1 : forall E H m base off e v,
  YP09.chunk_ok tfibsegs E (mrestrict H m) base (YP09.mkChunk off (CVal 1 e)) ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> aview tfibsegs H m (base + off) = Some (v mod 256).
Proof.
intros E H m base off e v Hc He Hv.
destruct (Hc 0 ltac:(cbn; lia)) as (b & Hb & Hm). cbn [YP09.c_off YP09.c_val cbyte] in Hb, Hm.
injection Hb as <-. rewrite Z.add_0_r in Hm. unfold aview. rewrite Hm. cbn [option_map]. f_equal.
unfold byte_of_word. rewrite He, Z.shiftr_0_r, Z_to_bv_unsigned, wz by exact Hv.
unfold bv_wrap. reflexivity.
Qed.

(* past_nul B's frame budget, stated ONCE and COMPUTED: the right-hand side is evaluated from STK_past_nul's
   definition at elaboration time, so a change to its components (FRAME_past_nul, STK_RT_ALLOC, STK_RT_INTRIN) needs
   no edit here or at any use. Every proof site below uses this lemma instead of re-asserting a numeral. *)
Lemma pn_stk : STK_past_nul = ltac:(let x := eval vm_compute in STK_past_nul in exact x).
Proof. reflexivity. Qed.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Abbreviation SKB := FSH_Base.fsB_sink_head.
Variable B : asyms.
Hypothesis IMG : fs_img_facts tfibsegs B.
Hypothesis HGOT : as_got_shadow B = tfib_D_GOT_asan_shadow_memory_dynamic_address.
Hypothesis HCELL : as_shadow_cell B = tfib_D_asan_shadow_memory_dynamic_address.
Hypothesis FS_ENV : api_env tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FR_MALLOC : pc_wrap_malloc (as_code B) = PC_malloc /\ FSupoisonU.amalloc_realizesU tfibsegs B.
Hypothesis FR_MEMCPY : FSupoisonU.aintrin_realizesU tfibsegs B OCpy PC_memcpy.
Hypothesis FR_MEMSET : FSupoisonU.aintrin_realizesU tfibsegs B OSet PC_memset.

(* the machine value of a register a run left as an sv whose value is known *)
Lemma pn_reg_U : forall (H : word -> bool) E ss ms (r : bv 5) v,
  st_ok tfibsegs E ss (restrict H ms) -> YP0e.U E (sr_get (ss_regs ss) r) = v -> getr (ms_regs ms) r = w64 v.
Proof.
intros H E ss ms r v HS Hv. rewrite (st_ok_restrict_reg tfibsegs _ _ _ _ r HS), denot_lit_U, Hv. reflexivity.
Qed.

(* ---- the frame: the eight saved registers at sp0 - 8 .. sp0 - 64 ---- *)
Definition pn_xs (regs : bvmap 5 word) : list word :=
  [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21; getr regs 22].
Definition pn_frame (H : word -> bool) (m : word -> option byte) (sp0 : Z) (regs : bvmap 5 word) : Prop :=
  val_mem tfibsegs (mrestrict H m) (sp0 - 8) 8 (bv_unsigned (getr regs 1)) /\
  val_mem tfibsegs (mrestrict H m) (sp0 - 16) 8 (bv_unsigned (getr regs 8)) /\
  val_mem tfibsegs (mrestrict H m) (sp0 - 24) 8 (bv_unsigned (getr regs 9)) /\
  val_mem tfibsegs (mrestrict H m) (sp0 - 32) 8 (bv_unsigned (getr regs 18)) /\
  val_mem tfibsegs (mrestrict H m) (sp0 - 40) 8 (bv_unsigned (getr regs 19)) /\
  val_mem tfibsegs (mrestrict H m) (sp0 - 48) 8 (bv_unsigned (getr regs 20)) /\
  val_mem tfibsegs (mrestrict H m) (sp0 - 56) 8 (bv_unsigned (getr regs 21)) /\
  val_mem tfibsegs (mrestrict H m) (sp0 - 64) 8 (bv_unsigned (getr regs 22)).
Lemma pn_frame_kept : forall H H' m m' sp0 regs, pn_frame H m sp0 regs ->
  (forall a, sp0 - 64 <= a < sp0 -> aview tfibsegs H' m' a = aview tfibsegs H m a) -> pn_frame H' m' sp0 regs.
Proof.
intros H H' m m' sp0 regs (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8) K.
unfold pn_frame. repeat split; (eapply val_mem_kept; [|eassumption]); intros k Hk; apply K; cbn in Hk; lia.
Qed.
Lemma pn_frame_cs : forall H m sp0 regs regs2, pn_frame H m sp0 regs ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs2 (fs_extraT ++ pn_xs regs)) (mrestrict H m) (sp0 - 64)) pn_cs.
Proof.
intros H m sp0 regs regs2 (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8).
assert (X : forall j r, (j < 9)%nat -> nth j (fs_extraT ++ pn_xs regs) (Z_to_bv 64 0) = r ->
  sv_denot (Ereg regs2 (fs_extraT ++ pn_xs regs)) (SOff (32 + j) 0) = Z_to_bv 64 (bv_unsigned r)).
{ intros j r Hj Hr. rewrite fsw_SOff0, ew_Ereg_extra, Hr. symmetry. apply Z_to_bv_bv_unsigned. }
unfold pn_cs. repeat constructor.
- apply (chunk_ok_val tfibsegs _ _ _ 56 8%N (SOff 33 0) (bv_unsigned (getr regs 1)));
    [exact (X 1%nat _ ltac:(lia) eq_refl) | apply u64_range | cbn; lia | replace (sp0 - 64 + 56) with (sp0 - 8) by lia; exact V1].
- apply (chunk_ok_val tfibsegs _ _ _ 48 8%N (SOff 34 0) (bv_unsigned (getr regs 8)));
    [exact (X 2%nat _ ltac:(lia) eq_refl) | apply u64_range | cbn; lia | replace (sp0 - 64 + 48) with (sp0 - 16) by lia; exact V2].
- apply (chunk_ok_val tfibsegs _ _ _ 40 8%N (SOff 35 0) (bv_unsigned (getr regs 9)));
    [exact (X 3%nat _ ltac:(lia) eq_refl) | apply u64_range | cbn; lia | replace (sp0 - 64 + 40) with (sp0 - 24) by lia; exact V3].
- apply (chunk_ok_val tfibsegs _ _ _ 32 8%N (SOff 36 0) (bv_unsigned (getr regs 18)));
    [exact (X 4%nat _ ltac:(lia) eq_refl) | apply u64_range | cbn; lia | replace (sp0 - 64 + 32) with (sp0 - 32) by lia; exact V4].
- apply (chunk_ok_val tfibsegs _ _ _ 24 8%N (SOff 37 0) (bv_unsigned (getr regs 19)));
    [exact (X 5%nat _ ltac:(lia) eq_refl) | apply u64_range | cbn; lia | replace (sp0 - 64 + 24) with (sp0 - 40) by lia; exact V5].
- apply (chunk_ok_val tfibsegs _ _ _ 16 8%N (SOff 38 0) (bv_unsigned (getr regs 20)));
    [exact (X 6%nat _ ltac:(lia) eq_refl) | apply u64_range | cbn; lia | replace (sp0 - 64 + 16) with (sp0 - 48) by lia; exact V6].
- apply (chunk_ok_val tfibsegs _ _ _ 8 8%N (SOff 39 0) (bv_unsigned (getr regs 21)));
    [exact (X 7%nat _ ltac:(lia) eq_refl) | apply u64_range | cbn; lia | replace (sp0 - 64 + 8) with (sp0 - 56) by lia; exact V7].
- apply (chunk_ok_val tfibsegs _ _ _ 0 8%N (SOff 40 0) (bv_unsigned (getr regs 22)));
    [exact (X 8%nat _ ltac:(lia) eq_refl) | apply u64_range | cbn; lia | replace (sp0 - 64 + 0) with (sp0 - 64) by lia; exact V8].
Qed.

Definition pn_entry_region : YP09.region :=
  YP09.mkRegion (Some 2%nat) (-64) 0 (-64) 0
    [YP09.mkChunk (-64) (CVal 8 (SOff 22 0)); YP09.mkChunk (-56) (CVal 8 (SOff 21 0));
     YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0));
     YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0));
     YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].
Lemma pn_frame_of_entry : forall regs H mm sp0,
  region_ok tfibsegs (Ereg regs fs_extraT) (mrestrict H mm) pn_entry_region ->
  bv_unsigned (ew (Ereg regs fs_extraT) 2) = sp0 -> pn_frame H mm sp0 regs.
Proof.
intros regs H mm sp0 HR Hsp.
assert (X : forall (r : nat) (q : bv 5), Z.of_nat r = bv_unsigned q ->
  sv_denot (Ereg regs fs_extraT) (SOff r 0) = Z_to_bv 64 (bv_unsigned (getr regs q))).
{ intros r q Hq. rewrite fsw_SOff0, (ew_Ereg_nat regs fs_extraT r q Hq). symmetry. apply Z_to_bv_bv_unsigned. }
unfold pn_frame, pn_entry_region in *.
repeat split.
- exact (fsw_field _ _ 2 sp0 _ _ _ _ _ (-8) 8%N (SOff 1 0) _ HR Hsp ltac:(cbn; tauto) (X 1%nat 1%bv eq_refl) (u64_range _) ltac:(cbn; lia)).
- exact (fsw_field _ _ 2 sp0 _ _ _ _ _ (-16) 8%N (SOff 8 0) _ HR Hsp ltac:(cbn; tauto) (X 8%nat 8%bv eq_refl) (u64_range _) ltac:(cbn; lia)).
- exact (fsw_field _ _ 2 sp0 _ _ _ _ _ (-24) 8%N (SOff 9 0) _ HR Hsp ltac:(cbn; tauto) (X 9%nat 9%bv eq_refl) (u64_range _) ltac:(cbn; lia)).
- exact (fsw_field _ _ 2 sp0 _ _ _ _ _ (-32) 8%N (SOff 18 0) _ HR Hsp ltac:(cbn; tauto) (X 18%nat 18%bv eq_refl) (u64_range _) ltac:(cbn; lia)).
- exact (fsw_field _ _ 2 sp0 _ _ _ _ _ (-40) 8%N (SOff 19 0) _ HR Hsp ltac:(cbn; tauto) (X 19%nat 19%bv eq_refl) (u64_range _) ltac:(cbn; lia)).
- exact (fsw_field _ _ 2 sp0 _ _ _ _ _ (-48) 8%N (SOff 20 0) _ HR Hsp ltac:(cbn; tauto) (X 20%nat 20%bv eq_refl) (u64_range _) ltac:(cbn; lia)).
- exact (fsw_field _ _ 2 sp0 _ _ _ _ _ (-56) 8%N (SOff 21 0) _ HR Hsp ltac:(cbn; tauto) (X 21%nat 21%bv eq_refl) (u64_range _) ltac:(cbn; lia)).
- exact (fsw_field _ _ 2 sp0 _ _ _ _ _ (-64) 8%N (SOff 22 0) _ HR Hsp ltac:(cbn; tauto) (X 22%nat 22%bv eq_refl) (u64_range _) ltac:(cbn; lia)).
Qed.
Lemma pn_frame_of_cs : forall E H m sp0 regs cs,
  (forall j, (j < 9)%nat -> ew E (32 + j) = nth j (fs_extraT ++ pn_xs regs) (Z_to_bv 64 0)) ->
  bv_unsigned (ew E 2) = sp0 - 64 ->
  (forall c, In c pn_cs -> In c cs) ->
  region_ok tfibsegs E (mrestrict H m) (fstk_ret 64 cs) -> pn_frame H m sp0 regs.
Proof.
intros E H m sp0 regs cs EX Hsp Hcs HR.
assert (X : forall j r, (j < 9)%nat -> nth j (fs_extraT ++ pn_xs regs) (Z_to_bv 64 0) = r ->
  sv_denot E (SOff (32 + j) 0) = Z_to_bv 64 (bv_unsigned r)).
{ intros j r Hj Hr. rewrite fsw_SOff0, EX, Hr by exact Hj. symmetry. apply Z_to_bv_bv_unsigned. }
unfold pn_frame, fstk_ret in *.
assert (I1 : forall off e, In (YP09.mkChunk off (CVal 8 e)) pn_cs -> In (YP09.mkChunk off (CVal 8 e)) cs) by (intros; apply Hcs; assumption).
repeat split.
- pose proof (fsw_field _ _ 2 (sp0 - 64) _ _ _ _ _ 56 8%N (SOff 33 0) _ HR Hsp ltac:(apply I1; cbn; tauto) (X 1%nat _ ltac:(lia) eq_refl) (u64_range _) ltac:(cbn; lia)) as V.
  replace (sp0 - 64 + 56) with (sp0 - 8) in V by lia. exact V.
- pose proof (fsw_field _ _ 2 (sp0 - 64) _ _ _ _ _ 48 8%N (SOff 34 0) _ HR Hsp ltac:(apply I1; cbn; tauto) (X 2%nat _ ltac:(lia) eq_refl) (u64_range _) ltac:(cbn; lia)) as V.
  replace (sp0 - 64 + 48) with (sp0 - 16) in V by lia. exact V.
- pose proof (fsw_field _ _ 2 (sp0 - 64) _ _ _ _ _ 40 8%N (SOff 35 0) _ HR Hsp ltac:(apply I1; cbn; tauto) (X 3%nat _ ltac:(lia) eq_refl) (u64_range _) ltac:(cbn; lia)) as V.
  replace (sp0 - 64 + 40) with (sp0 - 24) in V by lia. exact V.
- pose proof (fsw_field _ _ 2 (sp0 - 64) _ _ _ _ _ 32 8%N (SOff 36 0) _ HR Hsp ltac:(apply I1; cbn; tauto) (X 4%nat _ ltac:(lia) eq_refl) (u64_range _) ltac:(cbn; lia)) as V.
  replace (sp0 - 64 + 32) with (sp0 - 32) in V by lia. exact V.
- pose proof (fsw_field _ _ 2 (sp0 - 64) _ _ _ _ _ 24 8%N (SOff 37 0) _ HR Hsp ltac:(apply I1; cbn; tauto) (X 5%nat _ ltac:(lia) eq_refl) (u64_range _) ltac:(cbn; lia)) as V.
  replace (sp0 - 64 + 24) with (sp0 - 40) in V by lia. exact V.
- pose proof (fsw_field _ _ 2 (sp0 - 64) _ _ _ _ _ 16 8%N (SOff 38 0) _ HR Hsp ltac:(apply I1; cbn; tauto) (X 6%nat _ ltac:(lia) eq_refl) (u64_range _) ltac:(cbn; lia)) as V.
  replace (sp0 - 64 + 16) with (sp0 - 48) in V by lia. exact V.
- pose proof (fsw_field _ _ 2 (sp0 - 64) _ _ _ _ _ 8 8%N (SOff 39 0) _ HR Hsp ltac:(apply I1; cbn; tauto) (X 7%nat _ ltac:(lia) eq_refl) (u64_range _) ltac:(cbn; lia)) as V.
  replace (sp0 - 64 + 8) with (sp0 - 56) in V by lia. exact V.
- pose proof (fsw_field _ _ 2 (sp0 - 64) _ _ _ _ _ 0 8%N (SOff 40 0) _ HR Hsp ltac:(apply I1; cbn; tauto) (X 8%nat _ ltac:(lia) eq_refl) (u64_range _) ltac:(cbn; lia)) as V.
  replace (sp0 - 64 + 0) with (sp0 - 64) in V by lia. exact V.
Qed.

(* ---- the new block and the U-form views ---- *)
Lemma pn_unp_app : forall ly S U (W : world tfibsegs) mem md a, ARU tfibsegs B ly S U W mem md -> 0 <= a < 2 ^ 64 ->
  (a < SHADOW_OFF \/ kHighMemBeg <= a) -> unpoison U mem (Z_to_bv 64 a) = mem (Z_to_bv 64 a).
Proof.
intros ly S U W mem md a H Ha [Hl|Hh].
- apply (ARU_mem_low tfibsegs B ly S U W mem md); [exact H | rewrite wz by lia; exact Hl].
- apply (fsw_unpoison_high B ly S U W mem md a H). lia.
Qed.
Lemma pn_view_app : forall ly S U (W : world tfibsegs) mem md a, ARU tfibsegs B ly S U W mem md -> 0 <= a < 2 ^ 64 ->
  (a < SHADOW_OFF \/ kHighMemBeg <= a) -> aview tfibsegs (w_H W) (unpoison U mem) a = aview tfibsegs (w_H W) mem a.
Proof. intros. apply aview_at. eapply pn_unp_app; eassumption. Qed.
Lemma pn_ush_new : forall ly S U (W : world tfibsegs) mem md p q x, ARU tfibsegs B ly S U W mem md ->
  (forall b m, In (b, m) (ablocks B ly S) -> zdisjoint (b, req_size m) (p, q)) -> p <= x < p + q -> 0 <= x < 2 ^ 64 ->
  in_ush U (bv_unsigned (Z_to_bv 64 (shadow_addr x))) = false.
Proof.
intros ly S U W mem md p q x H Hd Hx Hx64. apply (ARU_shadow_out_block tfibsegs B ly S U W mem md x H Hx64).
intros b m Hb Hin. specialize (Hd b m Hb). unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.
Lemma pn_ra_raw : forall ly S U (W : world tfibsegs) m md p k a len, ARU tfibsegs B ly S U W m md ->
  In (p, k) (ablocks B ly S) -> p <= a -> a + len <= p + req_size k ->
  (forall x, a <= x < a + len -> in_ush U (bv_unsigned (Z_to_bv 64 (shadow_addr x))) = false) ->
  range_addressable (aview tfibsegs (w_H W) m) SHADOW_OFF a len.
Proof.
intros ly S U W m md p k a len H Hin H1 H2 Hu.
apply (range_addressable_agree (aview tfibsegs (w_H W) (unpoison U m))).
- intros x Hx. change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x).
  symmetry. apply (aview_unpoison_out tfibsegs). exact (Hu x Hx).
- exact (range_addressable_of_block tfibsegs B (AR_laws_ok tfibsegs B) ly S W (unpoison U m) md p k a len (ARU_AR _ _ _ _ _ _ _ _ H) Hin H1 H2).
Qed.
Lemma pn_hull_raw : forall ly S U (W : world tfibsegs) m md a len, ARU tfibsegs B ly S U W m md ->
  shadow_hull_vis (aview tfibsegs (w_H W) (unpoison U m)) a len -> shadow_hull_vis (aview tfibsegs (w_H W) m) a len.
Proof.
intros ly S U W m md a len (HAR & OK & PO) Hh s Hs.
rewrite aview_mod. destruct (in_ush U (s mod 2 ^ 64)) eqn:Ei.
- rewrite (PO _ Ei). discriminate.
- rewrite <- aview_mod. rewrite <- (aview_unpoison_out tfibsegs (w_H W) U m s); [exact (Hh s Hs)|].
  rewrite Z_to_bv_unsigned. exact Ei.
Qed.
Lemma pn_ush_src : forall (W : world tfibsegs) mem U d n, range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF d n ->
  upoisoned tfibsegs W mem U -> forall x, d <= x < d + n -> 0 <= x < 2 ^ 63 ->
  in_ush U (bv_unsigned (Z_to_bv 64 (shadow_addr x))) = false.
Proof.
intros W mem U d n Hra Hpo x Hx Hx0.
assert (Hs : 0 <= shadow_addr x < 2 ^ 64).
{ unfold shadow_addr, SHADOW_OFF. split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
  pose proof (Z.div_le_mono x (2 ^ 63) 8 ltac:(lia) ltac:(lia)). change (2 ^ 63 / 8) with (2 ^ 60) in H. lia. }
rewrite wz by exact Hs. destruct (in_ush U (shadow_addr x)) eqn:Ei; [|reflexivity].
exfalso. pose proof (Hpo _ Ei) as Hp. destruct (Hra x Hx) as (s & Hsv & Hok).
change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x) in Hsv. rewrite Hp in Hsv. injection Hsv as <-.
unfold saddr_ok in Hok. lia.
Qed.

(* the facts of the appended block (res, n + 18) at every ARU memory after the malloc *)
Definition pn_blk (ly S ly2 S2 : _) (U : list (Z * Z)) (W2 : world tfibsegs) (n res : Z) : Prop :=
  In (res, n + 18) (ablocks B ly2 S2) /\ ~ In (res, n + 18) (ablocks B ly S) /\
  4096 <= res /\ res mod 16 = 0 /\ res + n + 18 <= alloc_ceiling /\
  (res + (n + 18) <= 0x10000 \/ 0x5fd000 <= res) /\
  (forall x, res <= x < res + (n + 18) -> in_ush U (bv_unsigned (Z_to_bv 64 (shadow_addr x))) = false) /\
  (forall a, res <= a < res + (n + 18) -> 0 <= a < 2 ^ 64 /\ (a < SHADOW_OFF \/ kHighMemBeg <= a)) /\
  (forall m md', ARU tfibsegs B ly2 S2 U W2 m md' -> forall a, res <= a < res + (n + 18) ->
     apresent (w_H W2) m a /\ ~ aowned B ly2 S2 a) /\
  (forall m md' a len, ARU tfibsegs B ly2 S2 U W2 m md' -> res <= a -> a + len <= res + (n + 18) ->
     range_addressable (aview tfibsegs (w_H W2) m) SHADOW_OFF a len) /\
  (forall m md' a len, ARU tfibsegs B ly2 S2 U W2 m md' -> res <= a -> a + len <= res + (n + 18) -> 0 < len ->
     shadow_hull_vis (aview tfibsegs (w_H W2) m) a len) /\
  (forall m md' a len, ARU tfibsegs B ly2 S2 U W2 m md' -> res <= a -> a + len <= res + (n + 18) ->
     amem_range a len).
Lemma pn_blk_of : forall ly S U (W : world tfibsegs) mem md n res ly2 S2 (W2 : world tfibsegs) mem2 md2,
  0 <= n -> ARU tfibsegs B ly S U W mem md -> ARU tfibsegs B ly2 S2 U W2 mem2 md2 ->
  ablocks B ly2 S2 = ablocks B ly S ++ [(res, n + 18)] -> pn_blk ly S ly2 S2 U W2 n res.
Proof.
intros ly S U W mem md n res ly2 S2 W2 mem2 md2 Hn HARU HARU2 Hbl2.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hnew : In (res, n + 18) (ablocks B ly2 S2)) by (rewrite Hbl2; apply in_or_app; right; left; reflexivity).
pose proof (al_blocks _ _ LAWS ly2 S2 W2 (unpoison U mem2) md2 res (n + 18) (proj1 HARU2) Hnew)
  as (Hres16 & Hres4096 & Hresc & Hresapp & Hrespres & Hpw & _).
assert (Hreq : req_size (n + 18) = n + 18) by (unfold req_size; destruct (n + 18 =? 0) eqn:Ez; [apply Z.eqb_eq in Ez; lia | reflexivity]).
rewrite Hreq in Hresc, Hrespres.
assert (Hdisj : forall b m, In (b, m) (ablocks B ly S) -> zdisjoint (b, req_size m) (res, n + 18)).
{ intros b m Hb. apply in_split in Hb as (l1 & l2 & Ebq).
  pose proof (sep_blocks_pos tfibsegs B LAWS ly2 S2 W2 _ md2 (b, m) (res, n + 18) l1 l2 [] (proj1 HARU2)
    ltac:(rewrite Hbl2, Ebq, <- app_assoc; reflexivity)) as Hd.
  unfold zdisjoint, block_rng in *. cbn [fst snd] in *. rewrite Hreq in Hd. exact Hd. }
assert (Happ : forall a, res <= a < res + (n + 18) -> 0 <= a < 2 ^ 64 /\ (a < SHADOW_OFF \/ kHighMemBeg <= a)).
{ intros a Ha. unfold in_app, kLowShadowBeg, ASAN_CEIL in Hresapp. rewrite Hreq in Hresapp. unfold SHADOW_OFF. lia. }
assert (Hush : forall x, res <= x < res + (n + 18) -> in_ush U (bv_unsigned (Z_to_bv 64 (shadow_addr x))) = false).
{ intros x Hx. apply (pn_ush_new ly S U W mem md res (n + 18) x HARU Hdisj Hx). destruct (Happ x Hx). lia. }
assert (Hblk : forall m md', ARU tfibsegs B ly2 S2 U W2 m md' -> forall a, res <= a < res + (n + 18) ->
  apresent (w_H W2) m a /\ ~ aowned B ly2 S2 a).
{ intros m md' Hm a Ha.
  pose proof (al_blocks _ _ LAWS ly2 S2 W2 (unpoison U m) md' res (n + 18) (proj1 Hm) Hnew) as (_ & _ & _ & _ & Hp & _).
  rewrite Hreq in Hp. destruct (Hp a Ha) as [(Hh & b & Hb) Hno]. split; [|exact Hno].
  split; [exact Hh|]. exists b. rewrite <- (pn_unp_app ly2 S2 U W2 m md' a Hm (proj1 (Happ a Ha)) (proj2 (Happ a Ha))). exact Hb. }
unfold pn_blk. split; [exact Hnew|]. split.
{ intros Hin. specialize (Hdisj _ _ Hin). unfold zdisjoint in Hdisj. cbn [fst snd] in Hdisj. rewrite Hreq in Hdisj. lia. }
split; [exact Hres4096|]. split; [exact Hres16|]. split.
{ unfold in_app, kLowShadowBeg, ASAN_CEIL in Hresapp. rewrite Hreq in Hresapp. lia. }
split.
{ destruct (Z_le_gt_dec (res + (n + 18)) 0x10000) as [|H1]; [left; lia|].
  destruct (Z_le_gt_dec 0x5fd000 res) as [|H2]; [right; lia|]. exfalso.
  apply (blk_img tfibsegs B LAWS ly2 S2 W2 _ md2 res (n + 18) (Z.max res 0x10000) (proj1 HARU2) Hnew); [rewrite Hreq; lia|].
  apply pn_img. lia. }
split; [exact Hush|]. split; [exact Happ|]. split; [exact Hblk|]. split.
{ intros m md' a len Hm H1 H2. apply (pn_ra_raw ly2 S2 U W2 m md' res (n + 18) a len Hm Hnew H1); [rewrite Hreq; lia|].
  intros x Hx. apply Hush. lia. }
split.
{ intros m md' a len Hm H1 H2 H3. apply (pn_hull_raw ly2 S2 U W2 m md' a len Hm).
  apply (shadow_hull_vis_of_block tfibsegs B LAWS ly2 S2 W2 (unpoison U m) md' res (n + 18) a len (proj1 Hm) Hnew H1); [rewrite Hreq; lia | exact H3]. }
intros m md' a len Hm H1 H2.
exact (amem_range_of_block tfibsegs B LAWS ly2 S2 W2 _ md' res (n + 18) a len (proj1 Hm) Hnew H1 ltac:(rewrite Hreq; lia)).
Qed.

Definition pn_Q (U : list (Z * Z)) (ly : alayout) (S : astate) (n c res live peak cnt fail : Z) (db : list Z)
  : alayout -> astate -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' W' regs' mem' _ =>
    getr regs' 10 = w64 res /\ res <> 0 /\ res mod 16 = 0 /\
    ablocks B ly' S' = ablocks B ly S ++ [(res, n + 18)] /\
    fs_heads B ly' S' U /\ zbytes_at tfibsegs W' mem' res (pn_copy db c) /\
    fs_glob tfibsegs W' mem' live peak cnt fail.

Lemma pn_glob_kept : forall (W W' : world tfibsegs) mem mem' live peak cnt fail,
  fs_glob tfibsegs W mem live peak cnt fail ->
  (forall a, inFP FS_PSTAT_FP a -> aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a) ->
  fs_glob tfibsegs W' mem' live peak cnt fail.
Proof.
intros W W' mem mem' live peak cnt fail (G1 & G2 & G3 & G4 & GR) K.
assert (KV : forall g v, In (g, g + 8) FS_PSTAT_FP -> val_mem tfibsegs (mrestrict (w_H W) mem) g 8 v ->
  val_mem tfibsegs (mrestrict (w_H W') mem') g 8 v).
{ intros g v Hg Hv. apply (val_mem_kept tfibsegs (w_H W) (w_H W') mem mem' g 8 v); [|exact Hv].
  intros k Hk. apply K. apply (inFP_FS_PSTAT_FP g Hg). cbn in Hk. lia. }
unfold fs_glob, fs_glob_at. split; [|split; [|split; [|split]]].
- apply KV; [unfold FS_PSTAT_FP, G_LIVE; cbn; tauto | exact G1].
- apply KV; [unfold FS_PSTAT_FP, G_PEAK; cbn; tauto | exact G2].
- apply KV; [unfold FS_PSTAT_FP, G_COUNT; cbn; tauto | exact G3].
- apply KV; [unfold FS_PSTAT_FP, G_FAIL; cbn; tauto | exact G4].
- exact GR.
Qed.

(* the callee-saved registers at the `ret`: sp back up by the frame, s0 .. s6 reloaded from the frame (extra atoms
   34 .. 40), the rest the entry atoms *)
Definition pn_expect (r : bv 5) : sv :=
  match bv_unsigned r with 2 => SOff 2 64 | 8 => SOff 34 0 | 9 => SOff 35 0 | 18 => SOff 36 0
  | 19 => SOff 37 0 | 20 => SOff 38 0 | 21 => SOff 39 0 | 22 => SOff 40 0 | z => SOff (Z.to_nat z) 0 end.

(* ---- pn_tail: from the __asan_memset call 0x82930 (t + n + 1, 0, 16) to the `ret` ---- *)
Lemma pn_tail : forall ly S U (W : world tfibsegs) regs mem md n c (db : list Z) live peak cnt fail
    res ly2 S2 (W2 : world tfibsegs) regsT memT mdc,
  ret_ok (getr regs 1) -> fs_heads B ly S U -> fs_glob tfibsegs W mem live peak cnt fail ->
  0 <= c < 2 ^ 64 -> 0 <= n <= 2 ^ 22 -> Z.of_nat (length db) = n -> Forall (fun z => 0 <= z < 256) db ->
  ARU tfibsegs B ly S U W mem md ->
  ajournal (SK := SKB) tfibsegs B STK_past_nul (spZ regs) [] ly S W (unpoison U mem) md [] ly2 S2 W2
    (unpoison U memT) mdc 1 ->
  ARU tfibsegs B ly2 S2 U W2 memT mdc ->
  ablocks B ly2 S2 = ablocks B ly S ++ [(res, n + 18)] ->
  getr regsT 1 = Z_to_bv 64 RA_PN_MEMSET -> spZ regsT = spZ regs - 64 ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 10 = w64 (res + n + 1) -> getr regsT 11 = w64 0 -> getr regsT 12 = w64 16 ->
  getr regsT 8 = w64 res -> getr regsT 9 = w64 c -> getr regsT 18 = w64 (res + n) ->
  getr regsT 19 = w64 (res + n + 1) -> getr regsT 20 = w64 SHADOW_OFF ->
  getr regsT 21 = w64 (2 ^ 64 - 1 - res) -> getr regsT 22 = w64 (n + 17) ->
  (forall q, (q = 3 \/ q = 4 \/ 23 <= q <= 27) -> getr regsT (Z_to_bv 5 q) = getr regs (Z_to_bv 5 q)) ->
  pn_frame (w_H W2) memT (spZ regs) regs ->
  (forall i, 0 <= i < n -> aview tfibsegs (w_H W2) memT (res + i) = Some (nth (Z.to_nat i) db 0)) ->
  aview tfibsegs (w_H W2) memT (res + n) = Some 0 ->
  SRr tfibsegs W2 (mkCfg (mkst regsT (Z_to_bv 64 PC_memset) memT (seg_rom tfibsegs)) mdc)
    (fun W' c' => exists res0, apost_baseU (SK := SKB) tfibsegs B STK_past_nul [] regs ly S W mem md EV_past_nul U U
       (pn_Q U ly S n c res0 live peak cnt fail db) W' c').
Proof.
intros ly S U W regs mem md n c db live peak cnt fail res ly2 S2 W2 regsT memT mdc
  Hra FH HG Hc Hn Hlen Hdb HARU HJ HARU2 Hbl2 R1 Rsp R3 R4 R10 R11 R12 R8 R9 R18 R19 R20 R21 R22 Rcs PF Hbytes Hz.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof fs_segs_low as HSL. pose proof fs_wx as HWX.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR2 & _ & _ & _ & _ & _ & _ & _ & F1 & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof pn_stk as FS.
pose proof (pn_blk_of ly S U W mem md n res ly2 S2 W2 memT mdc ltac:(lia) HARU HARU2 Hbl2)
  as (Hnew & Hnotold & Hres4096 & Hres16 & Hresc & Hout & Hush & Happ & Hblk & Hra_new & Hhull_new & Hamem).
assert (Hreq : req_size (n + 18) = n + 18) by (unfold req_size; destruct (n + 18 =? 0) eqn:Ez; [apply Z.eqb_eq in Ez; lia | reflexivity]).
assert (Hraok : ret_ok (getr regsT 1)) by (rewrite R1; apply ret_ok_even; rewrite unsigned_lit_small by (unfold RA_PN_MEMSET; lia); reflexivity).
pose proof (fsw_ecall_preU_at (SK := SKB) B STK_past_nul (spZ regs) [] ly S W (unpoison U mem) md [] ly2 S2 U W2 memT mdc 1
  regsT (-64) HJ HARU2 ltac:(lia) eq_refl ltac:(lia) ltac:(unfold ESTACK; lia) Hraok R3 R4) as HPRE.
assert (HMS := FR_MEMSET ly2 S2 U W2 regsT memT mdc (res + n + 1) 0 16 HPRE R10 R11 R12 ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(intros a Ha; destruct (Hblk memT mdc HARU2 a ltac:(lia)) as [Hp Hno];
    split; [exact (apresent_writable tfibsegs _ _ _ Hp) | split; [exact Hno | rewrite Rsp; unfold ESTACK; lia]])
  (Hamem memT mdc (res + n + 1) 16 HARU2 ltac:(lia) ltac:(lia))
  (Hra_new memT mdc (res + n + 1) 16 HARU2 ltac:(lia) ltac:(lia))
  (fun _ => Hhull_new memT mdc (res + n + 1) 16 HARU2 ltac:(lia) ltac:(lia) ltac:(lia)) I).
set (Wr := fun a => (res + n + 1 <= a < res + n + 17) \/ (spZ regs - 64 - ESTACK <= a < spZ regs - 64)).
assert (HWR : forall a, Wr a -> awr_byte tfibsegs B STK_past_nul (spZ regs) [] (ablocks B ly S) (ablocks B ly2 S2) ly2 []
  (frames S) a).
{ intros a [Ha|Ha].
  - left. right. right. left. exists res, (n + 18). split; [exact Hnew|]. split; [exact Hnotold|]. rewrite Hreq. lia.
  - left. left. unfold ESTACK in Ha. lia. }
eapply SRr_bind.
{ refine (fsw_intrin_atU (SK := SKB) B STK_past_nul (spZ regs) [] ly S W (unpoison U mem) md [] ly2 S2 U W2 memT mdc 1 U Wr
    (getr regsT 1) _
    (fun regs' mem' md' => aregs_preserved regsT regs' /\
       (forall i, 0 <= i < 16 -> aview tfibsegs (w_H W2) mem' (res + n + 1 + i) = Some 0) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview tfibsegs (w_H W2) mem' a = aview tfibsegs (w_H W2) memT a)) HJ _ HWR).
  eapply SRr_mono; [exact HMS|]. intros W' c' _ (-> & regs' & mem' & md' & -> & HARU' & HP' & Hsb & H10' & Hset & Hfr & Hgr).
    split; [reflexivity|]. exists regs', mem', md'.
    split; [unfold cfg_at, raZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
    assert (HfrW : forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview tfibsegs (w_H W2) mem' a = aview tfibsegs (w_H W2) memT a).
    { intros a Ha HnW. apply Hfr; [exact Ha | intros X; apply HnW; left; lia | intros X; apply HnW; right; rewrite Rsp in X; lia]. }
    split; [exact HARU'|]. split; [exact Hsb|].
    split.
    { intros a Ha HnW. destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))) eqn:Ei; [apply aview_unpoison_in; exact Ei|].
      rewrite !(aview_unpoison_out tfibsegs _ U _ a Ei). exact (HfrW a Ha HnW). }
    split.
    { intros a (Hh & b & Hb). split; [exact Hh|].
      destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))) eqn:Ei; [rewrite unpoison_in by exact Ei; eexists; reflexivity|].
      rewrite unpoison_out in Hb |- * by exact Ei. exact (proj2 (Hgr a (conj Hh (ex_intro _ b Hb)))). }
    split; [exact HP'|]. split; [|exact HfrW].
    intros i Hi. rewrite (Hset i Hi). reflexivity.
  }
intros W3 c3 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HARU4 & HP4 & Hset4 & Hfr4).
rewrite R1.
assert (PF4 : pn_frame (w_H W2) mem4 (spZ regs) regs).
{ apply (pn_frame_kept _ _ _ _ _ regs PF). intros a Ha. apply Hfr4; [lia|]. unfold Wr, ESTACK. lia. }
assert (Esp4 : getr regs4 2 = getr regsT 2) by exact (HP4 2 ltac:(unfold acallee_saved; lia)).
assert (Usp4 : spZ regs4 = spZ regs - 64) by (unfold spZ at 1; rewrite Esp4; change (bv_unsigned (getr regsT 2)) with (spZ regsT); lia).
set (E4 := Ereg regs4 (fs_extraT ++ pn_xs regs)).
assert (G : forall (k : nat) (r : bv 5) v, Z.of_nat k = bv_unsigned r -> acallee_saved (bv_unsigned r) ->
  getr regsT r = Z_to_bv 64 v -> ew E4 k = Z_to_bv 64 v).
{ intros k r v Hk Hr Hv. subst E4. rewrite (ew_Ereg_nat regs4 _ k r Hk), (fsw_pres _ _ r HP4 Hr). exact Hv. }
assert (G8 : ew E4 8 = Z_to_bv 64 res) by exact (G 8%nat 8%bv _ eq_refl ltac:(pn_csv) R8).
assert (G9 : ew E4 9 = Z_to_bv 64 c) by exact (G 9%nat 9%bv _ eq_refl ltac:(pn_csv) R9).
assert (G18 : ew E4 18 = Z_to_bv 64 (res + n)) by exact (G 18%nat 18%bv _ eq_refl ltac:(pn_csv) R18).
assert (G19 : ew E4 19 = Z_to_bv 64 (res + n + 1)) by exact (G 19%nat 19%bv _ eq_refl ltac:(pn_csv) R19).
assert (G20 : ew E4 20 = Z_to_bv 64 SHADOW_OFF) by exact (G 20%nat 20%bv _ eq_refl ltac:(pn_csv) R20).
assert (G21 : ew E4 21 = Z_to_bv 64 (2 ^ 64 - 1 - res)) by exact (G 21%nat 21%bv _ eq_refl ltac:(pn_csv) R21).
assert (G22 : ew E4 22 = Z_to_bv 64 (n + 17)) by exact (G 22%nat 22%bv _ eq_refl ltac:(pn_csv) R22).
assert (E2c : bv_unsigned (ew E4 2) = spZ regs - 64) by (subst E4; rewrite (ew_Ereg_nat regs4 _ 2 2%bv eq_refl); exact Usp4).
assert (U18 : bv_unsigned (ew E4 18) = res + n) by (rewrite G18; apply wz; lia).
assert (U19 : bv_unsigned (ew E4 19) = res + n + 1) by (rewrite G19; apply wz; lia).
assert (U20 : bv_unsigned (ew E4 20) = SHADOW_OFF) by (rewrite G20; apply wz; unfold SHADOW_OFF; lia).
pose proof (fsw_resume_after_rtU_args_chunks (SK := SKB) B STK_past_nul (spZ regs) [] ly S W (unpoison U mem) md [] ly2 S2 U W2
  mem4 md4 1 regs4 64 (pn_xs regs) pn_cs pn_rs2 pn_gf2 RA_PN_MEMSET HGOT HCELL HJ4 HARU4 Usp4 ltac:(lia) ltac:(lia) eq_refl
  ltac:(vm_compute; reflexivity) (pn_frame_cs _ _ _ regs regs4 PF4)) as HS5.
fold E4 in HS5.
assert (RS5 : Forall (region_ok tfibsegs E4 (mrestrict (w_H W2) mem4)) pn_rs2).
{ unfold pn_rs2. apply Forall_cons; [|apply Forall_nil].
  unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U18. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
  intros o Ho; apply (apresent_writable tfibsegs); refine (proj1 (Hblk mem4 md4 HARU4 _ _)); lia. }
assert (PD5 : pairwise_disjoint E4 (fsT_ret_regions 64 pn_cs pn_rs2)).
{ apply pairwise_disjoint_of_extents.
  unfold fsT_ret_regions, pn_rs2, fstk_ret, fs_got_region, fs_bcell_region, extent_of_region.
  cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2c, U18.
  unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
assert (AO5 : atoms_ok E4 pn_gf2).
{ unfold pn_gf2, pn_af, pn_shf. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U18, U19, U20. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SHADOW_OFF. repeat split; try lia; exact I. }
specialize (HS5 RS5 PD5 AO5).
(* the run to the third UBSan guard 0x82934 *)
fsw_aj_runU pn_tbl_ok HS5 HJ4 HARU4.
{ unfold fss_retT, fsT_ret_regions, pn_rs2; cbn [ss_mem app].
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -64); pn_awr_side E2c.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen with (k := 18%nat) (b := res + n);
    lazymatch goal with
    | |- YP09.r_base _ = Some _ => reflexivity
    | |- bv_unsigned _ = _ => exact U18
    | |- awr_ok _ _ _ _ _ _ _ _ _ _ _ _ => apply awr_ok_nil
    | |- forall _, _ => cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; left; right; right; left; exists res, (n + 18);
                        split; [exact Hnew|]; split; [exact Hnotold|]; rewrite Hreq; lia
    end. }
lazymatch type of HS5 with st_ok _ _ _ (restrict _ ?mm) => rename mm into msA end.
apply (SRr_sym_branch tfibsegs W2 E4 _ msA _ _ BC_LTU (SOff 21 0) (SOff 22 0) HS5); intros Hb HS6;
  rewrite branch_ltu_U, (U_atom _ 21 _ G21 ltac:(lia)), (U_atom _ 22 _ G22 ltac:(lia)) in Hb;
  lazymatch type of Hb with
  | _ = true => exfalso; apply Z.ltb_lt in Hb; lia
  | _ = false => clear Hb HS5
  end.
(* U3 untaken: on to `add a0, s0, s6` 0x82938 *)
fsw_aj_run_toU pn_tbl_ok HS6 HJ4 HARU4 PN_ADD2.
{ cbn [add_cond ss_mem].
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -64); pn_awr_side E2c.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen with (k := 18%nat) (b := res + n);
    lazymatch goal with
    | |- YP09.r_base _ = Some _ => reflexivity
    | |- bv_unsigned _ = _ => exact U18
    | |- awr_ok _ _ _ _ _ _ _ _ _ _ _ _ => apply awr_ok_nil
    | |- forall _, _ => cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; left; right; right; left; exists res, (n + 18);
                        split; [exact Hnew|]; split; [exact Hnotold|]; rewrite Hreq; lia
    end. }
lazymatch type of HS6 with st_ok _ _ ?ss (restrict _ ?mm) => rename mm into msB;
  assert (Emem : ss_mem ss = fsT_ret_regions 64 pn_cs pn_rs2) by (vm_compute; reflexivity) end.
assert (Ha0 : getr (ms_regs msB) 10%bv = Z_to_bv 64 (res + n + 17)).
{ pn_sr HS6 (10%bv : bv 5). rewrite denot_lit_U. f_equal. replace (res + n + 17) with (res + (n + 17)) by lia.
  apply (pn_U_add E4 8 22 res (n + 17) G8 G22); lia. }
(* re-seat a0 = t + n + 17 on the fresh atom PN_A *)
pose proof (fsw_reseat_atom E4 _ (restrict (w_H W2) msB) 10%bv PN_A 0 1 pn_af HS6 ltac:(vm_compute; reflexivity)
  ltac:(intros X; apply (f_equal bv_unsigned) in X; vm_compute in X; discriminate X) ltac:(vm_compute; reflexivity)) as HR.
change (YK11.getr (ms_regs (restrict (w_H W2) msB)) 10%bv) with (YK11.getr (ms_regs msB) 10%bv) in HR.
rewrite Ha0 in HR. rewrite Emem in HR.
set (E5 := ewset E4 PN_A (Z_to_bv 64 (res + n + 17))) in HR.
assert (EW5 : forall k, k <> PN_A -> ew E5 k = ew E4 k) by (intros k Hk; subst E5; apply ew_ewset_other; exact Hk).
assert (U41 : bv_unsigned (ew E5 PN_A) = res + n + 17) by (subst E5; rewrite ew_ewset_same; apply wz; lia).
assert (E2c5 : bv_unsigned (ew E5 2) = spZ regs - 64) by (rewrite EW5 by (unfold PN_A; lia); exact E2c).
assert (U18' : bv_unsigned (ew E5 18) = res + n) by (rewrite EW5 by (unfold PN_A; lia); exact U18).
specialize (HR ltac:(unfold region_ok, pn_rseat; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict];
    rewrite U41; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
    intros o Ho; apply (apresent_writable tfibsegs); refine (proj1 (Hblk (ms_mem msB) _ HARU4 _ _)); lia)
  ltac:(unfold fsT_ret_regions, pn_rs2, fstk_ret, fs_got_region, fs_bcell_region, pn_rseat;
    cbn [all_disjoint app]; unfold extent_disjoint; cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi];
    rewrite U41, E2c5, U18';
    unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address;
    repeat match goal with |- _ /\ _ => split end; try exact I; lia)
  ltac:(unfold afact_ok, pn_af; cbn [af_lo af_hi af_al2]; rewrite U41, Z.pow_0_r, Z.mod_1_r; lia)).
assert (SHOK2 : sh_ok tfibsegs pn_Bx pn_SH2 E5 (mrestrict (w_H W2) (ms_mem msB))).
{ assert (UB : YP0e.U E5 pn_Bx = SHADOW_OFF).
  { unfold pn_Bx. apply (U_atom _ 20 SHADOW_OFF); [rewrite EW5 by (unfold PN_A; lia); exact G20 | unfold SHADOW_OFF; lia]. }
  assert (V41 : YP0e.U E5 (SOff PN_A 0) = res + n + 17) by (apply (U_atom _ PN_A); [subst E5; apply ew_ewset_same | lia]).
  assert (V18 : YP0e.U E5 (SOff 18 0) = res + n) by (apply (U_atom _ 18); [rewrite EW5 by (unfold PN_A; lia); exact G18 | lia]).
  assert (V19 : YP0e.U E5 (SOff 19 0) = res + n + 1) by (apply (U_atom _ 19); [rewrite EW5 by (unfold PN_A; lia); exact G19 | lia]).
  unfold sh_ok, pn_SH2. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]];
    unfold shent_ok, app_apart; cbn [she_m she_lo she_hi];
    change (rd_of tfibsegs (mrestrict (w_H W2) (ms_mem msB))) with (aview tfibsegs (w_H W2) (ms_mem msB));
    rewrite UB; rewrite ?V41, ?V18, ?V19;
    (split; [apply (Hra_new (ms_mem msB) _ _ _ HARU4); lia|]);
    intros a Ha; destruct (Happ a ltac:(lia)) as [_ Ha2]; unfold SHADOW_OFF in *; lia. }
(* the token run: the inline checks 0x82940 .. 0x82974, the three stores, to the `ret` *)
fsw_aj_run_tokU pn_tbl_ok HR HJ4 HARU4 SHOK2 fs_Bspan.
{ cbn [ss_mem add_atom].
  eapply awr_ok_cons_gen with (k := PN_A) (b := res + n + 17);
    lazymatch goal with
    | |- YP09.r_base _ = Some _ => reflexivity
    | |- bv_unsigned _ = _ => exact U41
    | |- awr_ok _ _ _ _ _ _ _ _ _ _ _ _ => idtac
    | |- forall _, _ => cbn [YP09.r_wlo YP09.r_whi pn_rseat]; intros a Ha; left; right; right; left; exists res, (n + 18);
                        split; [exact Hnew|]; split; [exact Hnotold|]; rewrite Hreq; lia
    end.
  unfold fsT_ret_regions, pn_rs2; cbn [app].
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -64); pn_awr_side E2c5.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen with (k := 18%nat) (b := res + n);
    lazymatch goal with
    | |- YP09.r_base _ = Some _ => reflexivity
    | |- bv_unsigned _ = _ => exact U18'
    | |- awr_ok _ _ _ _ _ _ _ _ _ _ _ _ => apply awr_ok_nil
    | |- forall _, _ => cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; left; right; right; left; exists res, (n + 18);
                        split; [exact Hnew|]; split; [exact Hnotold|]; rewrite Hreq; lia
    end. }
lazymatch type of HR with st_ok _ ?Ef _ (restrict _ ?mm) => set (E6 := Ef) in *; rename mm into msF end.
assert (EW6 : forall k, (k < 42)%nat -> ew E6 k = ew E5 k).
{ intros k Hk. subst E6. rewrite !ew_ewset_other by lia. reflexivity. }
assert (EX : forall j, (j < 9)%nat -> ew E4 (32 + j) = nth j (fs_extraT ++ pn_xs regs) (Z_to_bv 64 0)) by (intros j Hj; apply ew_Ereg_extra).
assert (EW64 : forall k, (k < 41)%nat -> ew E6 k = ew E4 k).
{ intros k Hk. rewrite EW6 by lia. apply EW5. unfold PN_A. lia. }
assert (EG : forall q : Z, (q = 3 \/ q = 4 \/ 23 <= q <= 27) -> ew E6 (Z.to_nat q) = getr regs (Z_to_bv 5 q)).
{ intros q Hq. rewrite EW64 by lia. subst E4. rewrite (ew_Ereg_nat regs4 _ (Z.to_nat q) (Z_to_bv 5 q)).
  - rewrite (fsw_pres _ _ (Z_to_bv 5 q) HP4); [exact (Rcs q Hq)|]. rewrite Z_to_bv_unsigned, bv_wrap_small; [unfold acallee_saved; lia|].
    unfold bv_modulus. cbn. lia.
  - rewrite Z_to_bv_unsigned, bv_wrap_small; [lia|]. unfold bv_modulus. cbn. lia. }
assert (Hjalr : v_jalr (getr (ms_regs msF) 1) 0 = getr regs 1).
{ pn_sr HR (1%bv : bv 5). rewrite fsw_SOff0, EW64 by lia. change 33%nat with (32 + 1)%nat. rewrite EX by lia. exact Hra. }
assert (HPf : aregs_preserved regs (ms_regs msF)).
{ apply (fsw_preserved _ E6 _ msF regs pn_expect HR); [vm_compute; reflexivity|].
  intros r Hr. cbv [CALLEE_SAVED In] in Hr.
  repeat (destruct Hr as [<-|Hr]); [..|destruct Hr];
  lazymatch goal with |- sv_denot _ (pn_expect ?q) = _ => let e := eval vm_compute in (pn_expect q) in change (pn_expect q) with e end.
  - apply bv_eq. rewrite denot_SOff, EW64 by lia. rewrite E2c. unfold spZ. rewrite zcanon_id; [lia|]. unfold M64.
    pose proof (u64_range (getr regs 2)). lia.
  - rewrite fsw_SOff0. exact (EG 3 ltac:(lia)).
  - rewrite fsw_SOff0. exact (EG 4 ltac:(lia)).
  - rewrite fsw_SOff0, EW64 by lia. change 34%nat with (32 + 2)%nat. rewrite EX by lia. reflexivity.
  - rewrite fsw_SOff0, EW64 by lia. change 35%nat with (32 + 3)%nat. rewrite EX by lia. reflexivity.
  - rewrite fsw_SOff0, EW64 by lia. change 36%nat with (32 + 4)%nat. rewrite EX by lia. reflexivity.
  - rewrite fsw_SOff0, EW64 by lia. change 37%nat with (32 + 5)%nat. rewrite EX by lia. reflexivity.
  - rewrite fsw_SOff0, EW64 by lia. change 38%nat with (32 + 6)%nat. rewrite EX by lia. reflexivity.
  - rewrite fsw_SOff0, EW64 by lia. change 39%nat with (32 + 7)%nat. rewrite EX by lia. reflexivity.
  - rewrite fsw_SOff0, EW64 by lia. change 40%nat with (32 + 8)%nat. rewrite EX by lia. reflexivity.
  - rewrite fsw_SOff0. exact (EG 23 ltac:(lia)).
  - rewrite fsw_SOff0. exact (EG 24 ltac:(lia)).
  - rewrite fsw_SOff0. exact (EG 25 ltac:(lia)).
  - rewrite fsw_SOff0. exact (EG 26 ltac:(lia)).
  - rewrite fsw_SOff0. exact (EG 27 ltac:(lia)). }
assert (Ra10 : getr (ms_regs msF) 10 = w64 res).
{ pn_sr HR (10%bv : bv 5). rewrite fsw_SOff0, EW64 by lia. exact G8. }
(* the stored bytes, from the final regions: [0] the re-seated t + n + 17, [4] s2's window [1, 3) *)
pose proof (fsw_region_nth E6 _ _ 0 _ HR eq_refl) as HR41. cbn [ms_mem restrict] in HR41.
pose proof (fsw_region_nth E6 _ _ 4 _ HR eq_refl) as HR18. cbn [ms_mem restrict] in HR18.
destruct HR41 as (_ & _ & _ & HC41). destruct HR18 as (_ & _ & _ & HC18).
cbn [YP09.r_base YP09.r_chunks] in HC41, HC18.
assert (B17 : aview tfibsegs (w_H W2) (ms_mem msF) (res + n + 17) = Some 0).
{ pose proof (pn_chunk1 E6 (w_H W2) (ms_mem msF) _ 0 (SLit 0) 0 (Forall_inv HC41) eq_refl ltac:(lia)) as H.
  assert (U41n : bv_unsigned (ew E5 41) = res + n + 17) by exact U41.
  cbn [base_val] in H. rewrite EW6, U41n, Z.add_0_r in H by lia. exact H. }
assert (B65 : aview tfibsegs (w_H W2) (ms_mem msF) (res + n + 2) = Some 65).
{ pose proof (pn_chunk1 E6 (w_H W2) (ms_mem msF) _ 2 (SLit 65) 65 (Forall_inv HC18) eq_refl ltac:(lia)) as H.
  cbn [base_val] in H. rewrite EW64, U18 in H by lia. exact H. }
assert (Bc : aview tfibsegs (w_H W2) (ms_mem msF) (res + n + 1) = Some (c mod 256)).
{ assert (Dc : sv_denot E6 (SOff 9 0) = Z_to_bv 64 c) by (rewrite fsw_SOff0, EW64 by lia; exact G9).
  pose proof (pn_chunk1 E6 (w_H W2) (ms_mem msF) _ 1 (SOff 9 0) c (Forall_inv (Forall_inv_tail HC18)) Dc Hc) as H.
  cbn [base_val] in H. rewrite EW64, U18 in H by lia. exact H. }
(* every other byte: the three runs' frames chain back to the memory after __asan_memset *)
cbn [ss_mem add_atom] in HF1.
assert (U41n : bv_unsigned (ew E5 41) = res + n + 17) by exact U41.
assert (NWR : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 64 <= a < spZ regs) -> ~ (res + n + 1 <= a < res + n + 3) ->
  ~ (res + n + 17 <= a < res + n + 18) -> aview tfibsegs (w_H W2) (ms_mem msF) a = aview tfibsegs (w_H W2) mem4 a).
{ intros a Ha N1 N2 N3.
  assert (X : forall (E : env) rs m m', frame_of E rs m m' ->
    (forall r, In r rs -> ~ (base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r)) ->
    aview tfibsegs (w_H W2) m' a = aview tfibsegs (w_H W2) m a).
  { intros E rs m m' Hfo Hno. apply aview_at. apply Hfo. rewrite wz by exact Ha. intros (r & Hin & Hr). exact (Hno r Hin Hr). }
  rewrite (X _ _ _ _ HF1); [rewrite (X _ _ _ _ HF0); [apply (X _ _ _ _ HF)|]|].
  all: intros r Hin; cbn [add_cond ss_mem fss_retT fsT_ret_regions pn_rs2 fstk_ret fs_got_region fs_bcell_region pn_rseat app In] in Hin;
    repeat destruct Hin as [<-|Hin]; try destruct Hin;
    cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi fstk_ret fs_got_region fs_bcell_region pn_rseat];
    rewrite ?E2c, ?U18, ?E2c5, ?U18', ?U41, ?U41n; lia. }
eapply SRr_mono.
{ apply (fsw_retU (SK := SKB) B pn_tbl pn_tbl_ok W2 E6 _ msF _ STK_past_nul (spZ regs) [] regs ly S U W mem md ly2 S2 U 1
    (pn_Q U ly S n c res live peak cnt fail db) HR eq_refl ltac:(vm_compute; reflexivity) Hjalr HJ4 HARU4 HPf).
  intros mat2. unfold pn_Q.
  split; [exact Ra10|]. split; [lia|]. split; [exact Hres16|]. split; [exact Hbl2|].
  split.
  { intros r Hr. destruct (FH r Hr) as (E16 & m & Hm & Hm16). split; [exact E16|]. exists m. split; [|exact Hm16].
    rewrite Hbl2. apply in_or_app. left. exact Hm. }
  split.
  { unfold zbytes_at. apply pn_garr8; [exact (pn_copy_bytes db c Hdb)|].
    intros j Hj. rewrite pn_copy_len in Hj.
    destruct (Nat.lt_ge_cases j (length db)) as [Hjn|Hjn].
    - rewrite pn_copy_head by exact Hjn. rewrite NWR by lia. rewrite Hfr4 by (unfold Wr, ESTACK; lia).
      replace j with (Z.to_nat (Z.of_nat j)) at 2 by lia. apply Hbytes. lia.
    - assert (Hk : exists k, j = (length db + k)%nat /\ (k < 18)%nat) by (exists (j - length db)%nat; lia).
      destruct Hk as (k & -> & Hk). rewrite pn_copy_tail by exact Hk.
      replace (res + Z.of_nat (length db + k)) with (res + n + Z.of_nat k) by lia.
      assert (Hk18 : (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/
        k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17)%nat) by lia.
      repeat destruct Hk18 as [->|Hk18]; [..|subst k]; cbn [nth app repeat Z.of_nat Pos.of_succ_nat Pos.succ];
      first [ exact Bc | exact B65 | exact B17
            | (rewrite Z.add_0_r, NWR by lia; rewrite Hfr4 by (unfold Wr, ESTACK; lia); exact Hz)
            | (rewrite NWR by lia;
               lazymatch goal with |- aview _ _ _ (res + n + ?z) = _ =>
                 replace (res + n + z) with (res + n + 1 + (z - 1)) by lia end;
               apply Hset4; lia) ]. }
  apply (pn_glob_kept W W2 mem (ms_mem msF) live peak cnt fail HG).
  intros a Ha.
  assert (Hai : 0x10000 <= a < 0x5fd000).
  { destruct Ha as (rr & Hrr & Hra'). unfold FS_PSTAT_FP in Hrr. cbn [In] in Hrr.
    repeat destruct Hrr as [<-|Hrr]; try destruct Hrr; cbn [fst snd] in Hra'; lia. }
  destruct (proj1 IMG a Ha) as [Hno Hne].
  pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
  rewrite <- (pn_view_app ly2 S2 U W2 (ms_mem msF) _ a HARU4) by (unfold SHADOW_OFF; lia).
  rewrite <- (pn_view_app ly S U W mem md a HARU) by (unfold SHADOW_OFF; lia).
  apply F3; lazymatch goal with
    | |- in_img _ _ => apply pn_img; exact Hai
    | |- ~ Exists _ _ => exact Hno
    | |- ~ inFP _ _ => intros X; exact (inFP_nil _ X)
    | |- fp_spares _ _ => apply fp_spares_closed; exact sink_closed_nil
    | |- ~ _ => exact Hne
    end. }
intros W' c' _ Hp. exists res. exact Hp.
Qed.

(* ---- pn_post: from the join 0x828f4 (after __asan_memcpy, or straight from `beqz s3` when n = 0) to the
   __asan_memset call 0x82930 ---- *)
Lemma pn_post : forall ly S U (W : world tfibsegs) regs mem md n c (db : list Z) live peak cnt fail
    res ly2 S2 (W2 : world tfibsegs) regsP memP mdc,
  ret_ok (getr regs 1) -> fs_heads B ly S U -> fs_glob tfibsegs W mem live peak cnt fail ->
  0 <= c < 2 ^ 64 -> 0 <= n <= 2 ^ 22 -> Z.of_nat (length db) = n -> Forall (fun z => 0 <= z < 256) db ->
  ARU tfibsegs B ly S U W mem md ->
  ajournal (SK := SKB) tfibsegs B STK_past_nul (spZ regs) [] ly S W (unpoison U mem) md [] ly2 S2 W2
    (unpoison U memP) mdc 1 ->
  ARU tfibsegs B ly2 S2 U W2 memP mdc ->
  ablocks B ly2 S2 = ablocks B ly S ++ [(res, n + 18)] ->
  spZ regsP = spZ regs - 64 ->
  getr regsP 3 = w64 (as_gp B) -> getr regsP 4 = w64 (as_tp B) ->
  getr regsP 8 = w64 res -> getr regsP 9 = w64 c -> getr regsP 19 = w64 n -> getr regsP 20 = w64 SHADOW_OFF ->
  (forall q, (q = 3 \/ q = 4 \/ 23 <= q <= 27) -> getr regsP (Z_to_bv 5 q) = getr regs (Z_to_bv 5 q)) ->
  pn_frame (w_H W2) memP (spZ regs) regs ->
  (forall i, 0 <= i < n -> aview tfibsegs (w_H W2) memP (res + i) = Some (nth (Z.to_nat i) db 0)) ->
  SRr tfibsegs W2 (mkCfg (mkst regsP (Z_to_bv 64 PN_JOIN) memP (seg_rom tfibsegs)) mdc)
    (fun W' c' => exists res0, apost_baseU (SK := SKB) tfibsegs B STK_past_nul [] regs ly S W mem md EV_past_nul U U
       (pn_Q U ly S n c res0 live peak cnt fail db) W' c').
Proof.
intros ly S U W regs mem md n c db live peak cnt fail res ly2 S2 W2 regsP memP mdc
  Hra FH HG Hc Hn Hlen Hdb HARU HJ HARU2 Hbl2 Rsp R3 R4 R8 R9 R19 R20 Rcs PF Hbytes.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof fs_segs_low as HSL. pose proof fs_wx as HWX.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR2 & _ & _ & _ & _ & _ & _ & _ & F1 & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof pn_stk as FS.
pose proof (pn_blk_of ly S U W mem md n res ly2 S2 W2 memP mdc ltac:(lia) HARU HARU2 Hbl2)
  as (Hnew & Hnotold & Hres4096 & Hres16 & Hresc & Hout & Hush & Happ & Hblk & Hra_new & Hhull_new & Hamem).
assert (Hreq : req_size (n + 18) = n + 18) by (unfold req_size; destruct (n + 18 =? 0) eqn:Ez; [apply Z.eqb_eq in Ez; lia | reflexivity]).
set (E := Ereg regsP (fs_extraT ++ pn_xs regs)).
assert (V : forall (k : nat) (r : bv 5) v, Z.of_nat k = bv_unsigned r -> getr regsP r = Z_to_bv 64 v -> ew E k = Z_to_bv 64 v).
{ intros k r v Hk Hv. subst E. rewrite (ew_Ereg_nat regsP _ k r Hk). exact Hv. }
assert (V8 : ew E 8 = Z_to_bv 64 res) by exact (V 8%nat 8%bv _ eq_refl R8).
assert (V9 : ew E 9 = Z_to_bv 64 c) by exact (V 9%nat 9%bv _ eq_refl R9).
assert (V19 : ew E 19 = Z_to_bv 64 n) by exact (V 19%nat 19%bv _ eq_refl R19).
assert (V20 : ew E 20 = Z_to_bv 64 SHADOW_OFF) by exact (V 20%nat 20%bv _ eq_refl R20).
assert (E2c : bv_unsigned (ew E 2) = spZ regs - 64) by (subst E; rewrite (ew_Ereg_nat regsP _ 2 2%bv eq_refl); exact Rsp).
assert (U20 : bv_unsigned (ew E 20) = SHADOW_OFF) by (rewrite V20; apply wz; unfold SHADOW_OFF; lia).
pose proof (fsw_resume_after_rtU_args_chunks (SK := SKB) B STK_past_nul (spZ regs) [] ly S W (unpoison U mem) md [] ly2 S2 U W2
  memP mdc 1 regsP 64 (pn_xs regs) pn_cs [] [pn_shf] PN_JOIN HGOT HCELL HJ HARU2 Rsp ltac:(lia) ltac:(lia) eq_refl
  ltac:(vm_compute; reflexivity) (pn_frame_cs _ _ _ regs regsP PF) (Forall_nil _)) as HS.
fold E in HS.
specialize (HS ltac:(apply pairwise_disjoint_of_extents;
    unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, extent_of_region;
    cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite E2c;
    unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address;
    cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd];
    repeat match goal with |- _ /\ _ => split end; try exact I; lia)
  ltac:(unfold pn_shf; cbn [atoms_ok]; unfold afact_ok; cbn [af_lo af_hi af_al2];
    rewrite U20, Z.pow_0_r, Z.mod_1_r; unfold SHADOW_OFF; repeat split; try lia; exact I)).
(* the run to the first UBSan guard 0x828f8 *)
fsw_aj_runU pn_tbl_ok HS HJ HARU2.
{ unfold fss_retT, fsT_ret_regions; cbn [ss_mem app].
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -64); pn_awr_side E2c.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch type of HS with st_ok _ _ _ (restrict _ ?mm) => rename mm into msA end.
apply (SRr_sym_branch tfibsegs W2 E _ msA _ _ BC_LTU (SAlu ALU_XOR (SOff 8 0) (SLit (-1))) (SOff 19 0) HS); intros Hb HS1;
  rewrite branch_ltu_U, (pn_U_not E 8 res V8 ltac:(lia)), (U_atom _ 19 _ V19 ltac:(lia)) in Hb;
  lazymatch type of Hb with
  | _ = true => exfalso; apply Z.ltb_lt in Hb; lia
  | _ = false => clear Hb HS
  end.
(* U1 untaken: on to `add s2, s0, s3` 0x828fc *)
fsw_aj_run_toU pn_tbl_ok HS1 HJ HARU2 PN_ADD1.
{ cbn [add_cond ss_mem].
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -64); pn_awr_side E2c.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch type of HS1 with st_ok _ _ ?ss (restrict _ ?mm) => rename mm into msB;
  assert (Emem : ss_mem ss = fsT_ret_regions 64 pn_cs []) by (vm_compute; reflexivity) end.
assert (Hs2 : getr (ms_regs msB) 18%bv = Z_to_bv 64 (res + n)).
{ pn_sr HS1 (18%bv : bv 5). rewrite denot_lit_U. f_equal. apply (pn_U_add E 8 19 res n V8 V19); lia. }
(* re-seat s2 = t + n on the fresh atom PN_A *)
pose proof (fsw_reseat_atom E _ (restrict (w_H W2) msB) 18%bv PN_A 0 1 pn_af HS1 ltac:(vm_compute; reflexivity)
  ltac:(intros X; apply (f_equal bv_unsigned) in X; vm_compute in X; discriminate X) ltac:(vm_compute; reflexivity)) as HR.
change (YK11.getr (ms_regs (restrict (w_H W2) msB)) 18%bv) with (YK11.getr (ms_regs msB) 18%bv) in HR.
rewrite Hs2 in HR. rewrite Emem in HR.
set (E5 := ewset E PN_A (Z_to_bv 64 (res + n))) in HR.
assert (EW5 : forall k, k <> PN_A -> ew E5 k = ew E k) by (intros k Hk; subst E5; apply ew_ewset_other; exact Hk).
assert (W41 : ew E5 PN_A = Z_to_bv 64 (res + n)) by (subst E5; apply ew_ewset_same).
assert (U41 : bv_unsigned (ew E5 PN_A) = res + n) by (rewrite W41; apply wz; lia).
assert (U41n : bv_unsigned (ew E5 41) = res + n) by exact U41.
assert (E2c5 : bv_unsigned (ew E5 2) = spZ regs - 64) by (rewrite EW5 by (unfold PN_A; lia); exact E2c).
specialize (HR ltac:(unfold region_ok, pn_rseat; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict];
    rewrite U41; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
    intros o Ho; apply (apresent_writable tfibsegs); refine (proj1 (Hblk (ms_mem msB) _ HARU2 _ _)); lia)
  ltac:(unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, pn_rseat;
    cbn [all_disjoint app]; unfold extent_disjoint; cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi];
    rewrite U41, E2c5;
    unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address;
    repeat match goal with |- _ /\ _ => split end; try exact I; lia)
  ltac:(unfold afact_ok, pn_af; cbn [af_lo af_hi af_al2]; rewrite U41, Z.pow_0_r, Z.mod_1_r; lia)).
assert (SHOK1 : sh_ok tfibsegs pn_Bx pn_SH1 E5 (mrestrict (w_H W2) (ms_mem msB))).
{ assert (UB : YP0e.U E5 pn_Bx = SHADOW_OFF).
  { unfold pn_Bx. apply (U_atom _ 20 SHADOW_OFF); [rewrite EW5 by (unfold PN_A; lia); exact V20 | unfold SHADOW_OFF; lia]. }
  assert (V41 : YP0e.U E5 (SOff PN_A 0) = res + n) by (apply (U_atom _ PN_A); [exact W41 | lia]).
  unfold sh_ok, pn_SH1. apply Forall_cons; [|apply Forall_nil].
  unfold shent_ok, app_apart; cbn [she_m she_lo she_hi].
  change (rd_of tfibsegs (mrestrict (w_H W2) (ms_mem msB))) with (aview tfibsegs (w_H W2) (ms_mem msB)).
  rewrite UB, V41.
  split; [apply (Hra_new (ms_mem msB) _ _ _ HARU2); lia|].
  intros a Ha; destruct (Happ a ltac:(lia)) as [_ Ha2]; unfold SHADOW_OFF in *; lia. }
(* the token run: the inline check 0x82900 .. 0x8290c, the store t[n] := 0 0x82914, U2 0x82918, to the memset call *)
fsw_aj_run_tokU pn_tbl_ok HR HJ HARU2 SHOK1 fs_Bspan.
{ cbn [ss_mem add_atom].
  eapply awr_ok_cons_gen with (k := PN_A) (b := res + n);
    lazymatch goal with
    | |- YP09.r_base _ = Some _ => reflexivity
    | |- bv_unsigned _ = _ => exact U41
    | |- awr_ok _ _ _ _ _ _ _ _ _ _ _ _ => idtac
    | |- forall _, _ => cbn [YP09.r_wlo YP09.r_whi pn_rseat]; intros a Ha; left; right; right; left; exists res, (n + 18);
                        split; [exact Hnew|]; split; [exact Hnotold|]; rewrite Hreq; lia
    end.
  unfold fsT_ret_regions; cbn [app].
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -64); pn_awr_side E2c5.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch type of HR with st_ok _ _ _ (restrict _ ?mm) => rename mm into msM end.
rewrite (st_ok_restrict_mkst tfibsegs (w_H W2) E5 _ msM HR eq_refl). cbn [ss_pc]. change 336428 with PC_memset.
(* the register file at the memset call *)
assert (VQ : forall k : nat, (k = 3 \/ k = 4 \/ 23 <= k <= 27)%nat -> ew E5 k = getr regs (Z_to_bv 5 (Z.of_nat k))).
{ intros k Hk. rewrite EW5 by (unfold PN_A; lia). subst E.
  assert (Hu : Z.of_nat k = bv_unsigned (Z_to_bv 5 (Z.of_nat k))) by (rewrite Z_to_bv_unsigned, bv_wrap_small; [lia|]; unfold bv_modulus; cbn; lia).
  rewrite (ew_Ereg_nat regsP _ k _ Hu). apply Rcs. lia. }
assert (W8 : ew E5 8 = Z_to_bv 64 res) by (rewrite EW5 by (unfold PN_A; lia); exact V8).
assert (W9 : ew E5 9 = Z_to_bv 64 c) by (rewrite EW5 by (unfold PN_A; lia); exact V9).
assert (W19 : ew E5 19 = Z_to_bv 64 n) by (rewrite EW5 by (unfold PN_A; lia); exact V19).
assert (W20 : ew E5 20 = Z_to_bv 64 SHADOW_OFF) by (rewrite EW5 by (unfold PN_A; lia); exact V20).
assert (W41n : ew E5 41 = Z_to_bv 64 (res + n)) by exact W41.
assert (T1 : getr (ms_regs msM) 1 = Z_to_bv 64 RA_PN_MEMSET)
  by exact (fsw_reg_lit _ E5 _ msM 1%bv RA_PN_MEMSET HR ltac:(vm_compute; reflexivity) ltac:(unfold RA_PN_MEMSET; lia)).
assert (T2 : spZ (ms_regs msM) = spZ regs - 64) by (unfold spZ at 1; pn_sr HR (2%bv : bv 5); rewrite fsw_SOff0; exact E2c5).
assert (T3 : getr (ms_regs msM) 3 = w64 (as_gp B)).
{ pn_sr HR (3%bv : bv 5). rewrite fsw_SOff0, (VQ 3%nat ltac:(lia)). transitivity (getr regsP 3); [symmetry; exact (Rcs 3 ltac:(lia)) | exact R3]. }
assert (T4 : getr (ms_regs msM) 4 = w64 (as_tp B)).
{ pn_sr HR (4%bv : bv 5). rewrite fsw_SOff0, (VQ 4%nat ltac:(lia)). transitivity (getr regsP 4); [symmetry; exact (Rcs 4 ltac:(lia)) | exact R4]. }
assert (T10 : getr (ms_regs msM) 10 = w64 (res + n + 1)) by pn_val HR (10%bv : bv 5) E5.
assert (T11 : getr (ms_regs msM) 11 = w64 0) by pn_val HR (11%bv : bv 5) E5.
assert (T12 : getr (ms_regs msM) 12 = w64 16) by pn_val HR (12%bv : bv 5) E5.
assert (T8 : getr (ms_regs msM) 8 = w64 res) by pn_val HR (8%bv : bv 5) E5.
assert (T9 : getr (ms_regs msM) 9 = w64 c) by pn_val HR (9%bv : bv 5) E5.
assert (T18 : getr (ms_regs msM) 18 = w64 (res + n)) by pn_val HR (18%bv : bv 5) E5.
assert (T19 : getr (ms_regs msM) 19 = w64 (res + n + 1)) by pn_val HR (19%bv : bv 5) E5.
assert (T20 : getr (ms_regs msM) 20 = w64 SHADOW_OFF) by pn_val HR (20%bv : bv 5) E5.
assert (T21 : getr (ms_regs msM) 21 = w64 (2 ^ 64 - 1 - res)).
{ apply (pn_reg_U _ E5 _ msM 21%bv _ HR).
  lazymatch goal with |- context [sr_get ?l ?q] => let v := eval vm_compute in (sr_get l q) in change (sr_get l q) with v end.
  exact (pn_U_not E5 8 res W8 ltac:(lia)). }
assert (T22 : getr (ms_regs msM) 22 = w64 (n + 17)) by pn_val HR (22%bv : bv 5) E5.
assert (TQ : forall q, (q = 3 \/ q = 4 \/ 23 <= q <= 27) -> getr (ms_regs msM) (Z_to_bv 5 q) = getr regs (Z_to_bv 5 q))
  by pn_rcsv HR VQ.
assert (EX5 : forall j, (j < 9)%nat -> ew E5 (32 + j) = nth j (fs_extraT ++ pn_xs regs) (Z_to_bv 64 0)).
{ intros j Hj. rewrite EW5 by (unfold PN_A; lia). apply ew_Ereg_extra. }
pose proof (fsw_region_nth E5 _ _ 1 _ HR eq_refl) as HRf. cbn [ms_mem restrict] in HRf.
pose proof (pn_frame_of_cs E5 _ _ _ regs _ EX5 E2c5 (fun c0 Hc0 => Hc0) HRf) as TF.
pose proof (fsw_region_nth E5 _ _ 0 _ HR eq_refl) as HR41. cbn [ms_mem restrict] in HR41.
destruct HR41 as (_ & _ & _ & HC41). cbn [YP09.r_base YP09.r_chunks] in HC41.
assert (Tz : aview tfibsegs (w_H W2) (ms_mem msM) (res + n) = Some 0).
{ pose proof (pn_chunk1 E5 (w_H W2) (ms_mem msM) _ 0 (SLit 0) 0 (Forall_inv HC41) eq_refl ltac:(lia)) as H.
  cbn [base_val] in H. rewrite U41n, Z.add_0_r in H. exact H. }
(* the copied bytes [t, t + n): no write window of the three runs reaches them *)
cbn [ss_mem add_atom] in HF1.
assert (Tb : forall i, 0 <= i < n -> aview tfibsegs (w_H W2) (ms_mem msM) (res + i) = Some (nth (Z.to_nat i) db 0)).
{ intros i Hi. rewrite <- (Hbytes i Hi).
  assert (Ha : 0 <= res + i < 2 ^ 64) by lia.
  assert (X : forall (E' : env) rs m m', frame_of E' rs m m' ->
    (forall r, In r rs -> ~ (base_val E' (YP09.r_base r) + YP09.r_wlo r <= res + i < base_val E' (YP09.r_base r) + YP09.r_whi r)) ->
    aview tfibsegs (w_H W2) m' (res + i) = aview tfibsegs (w_H W2) m (res + i)).
  { intros E' rs m m' Hfo Hno. apply aview_at. apply Hfo. rewrite wz by exact Ha. intros (r & Hin & Hr). exact (Hno r Hin Hr). }
  rewrite (X _ _ _ _ HF1); [rewrite (X _ _ _ _ HF0); [apply (X _ _ _ _ HF)|]|].
  all: intros r Hin; cbn [add_cond ss_mem fss_retT fsT_ret_regions fstk_ret fs_got_region fs_bcell_region pn_rseat app In] in Hin;
    repeat destruct Hin as [<-|Hin]; try destruct Hin;
    cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi fstk_ret fs_got_region fs_bcell_region pn_rseat];
    rewrite ?E2c, ?E2c5, ?U41, ?U41n; lia. }
eapply SRr_mono.
{ exact (pn_tail ly S U W regs mem md n c db live peak cnt fail res ly2 S2 W2 (ms_regs msM) (ms_mem msM) _
    Hra FH HG Hc Hn Hlen Hdb HARU HJ HARU2 Hbl2 T1 T2 T3 T4 T10 T11 T12 T8 T9 T18 T19 T20 T21 T22 TQ TF Tb Tz). }
intros W' c' _ Hp. exact Hp.
Qed.

(* ---- pn_mid: the __asan_memcpy call 0x828f0 (t, d, n), n > 0, back to the join 0x828f4 ---- *)
Lemma pn_mid : forall ly S U (W : world tfibsegs) regs mem md n c (db : list Z) live peak cnt fail
    res ly2 S2 (W2 : world tfibsegs) regsC memC mdc d b m,
  ret_ok (getr regs 1) -> fs_heads B ly S U -> fs_glob tfibsegs W mem live peak cnt fail ->
  0 <= c < 2 ^ 64 -> 0 < n <= 2 ^ 22 -> Z.of_nat (length db) = n -> Forall (fun z => 0 <= z < 256) db ->
  ARU tfibsegs B ly S U W mem md ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF d n -> amem_range d n -> 4096 <= d -> d + n + 8 <= alloc_ceiling ->
  In (b, m) (ablocks B ly S) -> b <= d -> d + n <= b + m ->
  (forall i, 0 <= i < n -> aview tfibsegs (w_H W) mem (d + i) = Some (nth (Z.to_nat i) db 0)) ->
  ajournal (SK := SKB) tfibsegs B STK_past_nul (spZ regs) [] ly S W (unpoison U mem) md [] ly2 S2 W2
    (unpoison U memC) mdc 1 ->
  ARU tfibsegs B ly2 S2 U W2 memC mdc ->
  ablocks B ly2 S2 = ablocks B ly S ++ [(res, n + 18)] ->
  getr regsC 1 = Z_to_bv 64 PN_JOIN -> spZ regsC = spZ regs - 64 ->
  getr regsC 3 = w64 (as_gp B) -> getr regsC 4 = w64 (as_tp B) ->
  getr regsC 10 = w64 res -> getr regsC 11 = w64 d -> getr regsC 12 = w64 n ->
  getr regsC 8 = w64 res -> getr regsC 9 = w64 c -> getr regsC 19 = w64 n -> getr regsC 20 = w64 SHADOW_OFF ->
  (forall q, (q = 3 \/ q = 4 \/ 23 <= q <= 27) -> getr regsC (Z_to_bv 5 q) = getr regs (Z_to_bv 5 q)) ->
  pn_frame (w_H W2) memC (spZ regs) regs ->
  SRr tfibsegs W2 (mkCfg (mkst regsC (Z_to_bv 64 PC_memcpy) memC (seg_rom tfibsegs)) mdc)
    (fun W' c' => exists res0, apost_baseU (SK := SKB) tfibsegs B STK_past_nul [] regs ly S W mem md EV_past_nul U U
       (pn_Q U ly S n c res0 live peak cnt fail db) W' c').
Proof.
intros ly S U W regs mem md n c db live peak cnt fail res ly2 S2 W2 regsC memC mdc d b m
  Hra FH HG Hc Hn Hlen Hdb HARU Hdra Hdam Hd4 Hdc Hbm Hbd Hdn Hsrc HJ HARU2 Hbl2
  R1 Rsp R3 R4 R10 R11 R12 R8 R9 R19 R20 Rcs PF.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof fs_segs_low as HSL. pose proof fs_wx as HWX.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR2 & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof pn_stk as FS.
pose proof (pn_blk_of ly S U W mem md n res ly2 S2 W2 memC mdc ltac:(lia) HARU HARU2 Hbl2)
  as (Hnew & Hnotold & Hres4096 & Hres16 & Hresc & Hout & Hush & Happ & Hblk & Hra_new & Hhull_new & Hamem).
assert (Hreq : req_size (n + 18) = n + 18) by (unfold req_size; destruct (n + 18 =? 0) eqn:Ez; [apply Z.eqb_eq in Ez; lia | reflexivity]).
assert (Hbm2 : In (b, m) (ablocks B ly2 S2)) by (rewrite Hbl2; apply in_or_app; left; exact Hbm).
pose proof (al_blocks _ _ LAWS ly2 S2 W2 (unpoison U memC) mdc b m HAR2 Hbm2)
  as (Hb16 & Hb4096 & Hbc & Hbapp & Hbpres & _ & Hbmx).
assert (Hreqm : m <= req_size m) by (unfold req_size; destruct (m =? 0) eqn:Ez; [apply Z.eqb_eq in Ez|]; lia).
assert (Hsd : res + n <= d \/ d + n <= res).
{ apply in_split in Hbm as (l1 & l2 & Ebq).
  pose proof (sep_blocks_pos tfibsegs B LAWS ly2 S2 W2 _ mdc (b, m) (res, n + 18) l1 l2 [] HAR2
    ltac:(rewrite Hbl2, Ebq, <- app_assoc; reflexivity)) as Hd.
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. rewrite Hreq in Hd. lia. }
assert (Bapp : forall a, b <= a < b + req_size m -> 0 <= a < 2 ^ 64 /\ (a < SHADOW_OFF \/ kHighMemBeg <= a)).
{ intros a Ha. unfold in_app, kLowShadowBeg, ASAN_CEIL in Hbapp. unfold SHADOW_OFF. lia. }
(* the source bytes at the call: the journal keeps the old block (b, m) *)
assert (HsrcC : forall i, 0 <= i < n -> aview tfibsegs (w_H W2) memC (d + i) = Some (nth (Z.to_nat i) db 0)).
{ intros i Hi. destruct (Bapp (d + i) ltac:(lia)) as [B1 B2].
  rewrite <- (pn_view_app ly2 S2 U W2 memC mdc (d + i) HARU2 B1 B2).
  replace (d + i) with (b + (d + i - b)) by lia.
  rewrite (F2 b m (d + i - b) Hbm Hbm2 ltac:(lia) ltac:(intros X; exact (inFP_nil _ X))).
  replace (b + (d + i - b)) with (d + i) by lia.
  rewrite (pn_view_app ly S U W mem md (d + i) HARU B1 B2). exact (Hsrc i Hi). }
assert (Hraok : ret_ok (getr regsC 1)) by (rewrite R1; apply ret_ok_even; rewrite unsigned_lit_small by (unfold PN_JOIN; lia); reflexivity).
pose proof (fsw_ecall_preU_at (SK := SKB) B STK_past_nul (spZ regs) [] ly S W (unpoison U mem) md [] ly2 S2 U W2 memC mdc 1
  regsC (-64) HJ HARU2 ltac:(lia) eq_refl ltac:(lia) ltac:(unfold ESTACK; lia) Hraok R3 R4) as HPRE.
assert (HMC := FR_MEMCPY ly2 S2 U W2 regsC memC mdc res d n HPRE R10 R11 R12 ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(intros a Ha; destruct (Hblk memC mdc HARU2 a ltac:(lia)) as [Hp Hno];
    split; [exact (apresent_writable tfibsegs _ _ _ Hp) | split; [exact Hno | rewrite Rsp; unfold ESTACK; lia]])
  (Hamem memC mdc res n HARU2 ltac:(lia) ltac:(lia))
  (Hra_new memC mdc res n HARU2 ltac:(lia) ltac:(lia))
  (fun Hn0 => Hhull_new memC mdc res n HARU2 ltac:(lia) ltac:(lia) Hn0)).
specialize (HMC ltac:(split; [lia|]; split; [lia|]; split;
  [ intros a Ha; split; [replace a with (d + (a - d)) by lia; rewrite (HsrcC (a - d)) by lia; discriminate | rewrite Rsp; unfold ESTACK; lia]
  | split; [exact Hsd|]; split; [exact Hdam|]; split;
    [ apply (pn_ra_raw ly2 S2 U W2 memC mdc b m d n HARU2 Hbm2 Hbd ltac:(lia)); intros x Hx; apply (pn_ush_src W mem U d n Hdra (proj2 (proj2 HARU)) x Hx); lia
    | intros Hn0; apply (pn_hull_raw ly2 S2 U W2 memC mdc d n HARU2);
      exact (shadow_hull_vis_of_block tfibsegs B LAWS ly2 S2 W2 _ mdc b m d n HAR2 Hbm2 Hbd ltac:(lia) Hn0) ] ])).
set (Wr := fun a => (res <= a < res + n) \/ (spZ regs - 64 - ESTACK <= a < spZ regs - 64)).
assert (HWR : forall a, Wr a -> awr_byte tfibsegs B STK_past_nul (spZ regs) [] (ablocks B ly S) (ablocks B ly2 S2) ly2 []
  (frames S) a).
{ intros a [Ha|Ha].
  - left. right. right. left. exists res, (n + 18). split; [exact Hnew|]. split; [exact Hnotold|]. rewrite Hreq. lia.
  - left. left. unfold ESTACK in Ha. lia. }
eapply SRr_bind.
{ refine (fsw_intrin_atU (SK := SKB) B STK_past_nul (spZ regs) [] ly S W (unpoison U mem) md [] ly2 S2 U W2 memC mdc 1 U Wr
    (getr regsC 1) _
    (fun regs' mem' md' => aregs_preserved regsC regs' /\
       (forall i, 0 <= i < n -> aview tfibsegs (w_H W2) mem' (res + i) = Some (nth (Z.to_nat i) db 0)) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview tfibsegs (w_H W2) mem' a = aview tfibsegs (w_H W2) memC a)) HJ _ HWR).
  eapply SRr_mono; [exact HMC|]. intros W' c' _ (-> & regs' & mem' & md' & -> & HARU' & HP' & Hsb & H10' & Hcpy & Hfr & Hgr).
    split; [reflexivity|]. exists regs', mem', md'.
    split; [unfold cfg_at, raZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
    assert (HfrW : forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview tfibsegs (w_H W2) mem' a = aview tfibsegs (w_H W2) memC a).
    { intros a Ha HnW. apply Hfr; [exact Ha | intros X; apply HnW; left; lia | intros X; apply HnW; right; rewrite Rsp in X; lia]. }
    split; [exact HARU'|]. split; [exact Hsb|].
    split.
    { intros a Ha HnW. destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))) eqn:Ei; [apply aview_unpoison_in; exact Ei|].
      rewrite !(aview_unpoison_out tfibsegs _ U _ a Ei). exact (HfrW a Ha HnW). }
    split.
    { intros a (Hh & bb & Hb). split; [exact Hh|].
      destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))) eqn:Ei; [rewrite unpoison_in by exact Ei; eexists; reflexivity|].
      rewrite unpoison_out in Hb |- * by exact Ei. exact (proj2 (Hgr a (conj Hh (ex_intro _ bb Hb)))). }
    split; [exact HP'|]. split; [|exact HfrW].
    intros i Hi. rewrite (Hcpy i Hi). exact (HsrcC i Hi).
  }
intros W3 c3 _ (-> & regs6 & mem6 & md6 & -> & HJ6 & HARU6 & HP6 & Hcp6 & Hfr6).
rewrite R1.
assert (PF6 : pn_frame (w_H W2) mem6 (spZ regs) regs).
{ apply (pn_frame_kept _ _ _ _ _ regs PF). intros a Ha. apply Hfr6; [lia|]. unfold Wr, ESTACK. lia. }
assert (Q6 : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs6 r = getr regsC r)
  by (intros r Hr; exact (fsw_pres _ _ r HP6 Hr)).
assert (Usp6 : spZ regs6 = spZ regs - 64) by (unfold spZ at 1; rewrite (Q6 2%bv ltac:(pn_csv)); exact Rsp).
assert (Rcs6 : forall q, (q = 3 \/ q = 4 \/ 23 <= q <= 27) -> getr regs6 (Z_to_bv 5 q) = getr regs (Z_to_bv 5 q)).
{ intros q Hq. rewrite Q6; [exact (Rcs q Hq)|]. rewrite Z_to_bv_unsigned, bv_wrap_small; [unfold acallee_saved; lia|].
  unfold bv_modulus. cbn. lia. }
exact (pn_post ly S U W regs mem md n c db live peak cnt fail res ly2 S2 W2 regs6 mem6 md6
  Hra FH HG Hc ltac:(lia) Hlen Hdb HARU HJ6 HARU6 Hbl2 Usp6
  ltac:(rewrite (Q6 3%bv ltac:(pn_csv)); exact R3) ltac:(rewrite (Q6 4%bv ltac:(pn_csv)); exact R4)
  ltac:(rewrite (Q6 8%bv ltac:(pn_csv)); exact R8) ltac:(rewrite (Q6 9%bv ltac:(pn_csv)); exact R9)
  ltac:(rewrite (Q6 19%bv ltac:(pn_csv)); exact R19) ltac:(rewrite (Q6 20%bv ltac:(pn_csv)); exact R20)
  Rcs6 PF6 Hcp6).
Qed.

Theorem past_nul_ok : @past_nul_spec fx rc SKB tfibsegs B.
Proof.
intros ly S U W regs mem md ch d n c db live peak cnt fail HPRE FH H10 H11 H12 Hc Hn Hlen HSRC HBLK HG HQ Hev Hlv Hmx.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof fs_segs_low as HSL. pose proof fs_wx as HWX.
destruct HPRE as [HAPU HRO]. destruct FR_MALLOC as [HMPC AMALLOC].
pose proof (fsw_sp B _ ly S U W regs mem md ch HAPU) as (Hal16 & Hceil & H47 & HS0).
pose proof (fsw_ARU B _ ly S U W regs mem md ch HAPU) as HARU.
pose proof HARU as HARU0.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HAPU as (HAP & HOK & HPO).
pose proof HAP as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof pn_stk as FS.
pose proof (fsw_entryT B STK_past_nul 64 ly S U W regs mem md ch A_past_nul HGOT HCELL HAPU ltac:(lia) ltac:(vm_compute; reflexivity)) as HS.
pose proof (ajournal_init (SK := SKB) tfibsegs B STK_past_nul [] ly S W regs (unpoison U mem) md ch HAP) as HJ.
set (E := Ereg regs fs_extraT) in HS.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs fs_extraT 2 2%bv eq_refl); reflexivity).
unfold cfg_at. change (w64 A_past_nul) with (Z_to_bv 64 A_past_nul).
(* ---- the entry run to `jal __wrap_malloc` 0x828d4 ---- *)
fsw_aj_run_toU pn_tbl_ok HS HJ HARU PC_malloc.
{ unfold fss0T, fsT_regions; cbn [ss_mem].
  eapply awr_ok_cons_stack with (n := 2%nat); pn_awr_side Usp.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
pose proof (fsw_reg_lit _ E _ ms 1%bv RA_PN_MALLOC HS ltac:(vm_compute; reflexivity) ltac:(unfold RA_PN_MALLOC; lia)) as R1.
pose proof (fsw_reg_off _ E _ ms 2%bv 2 (-64) (spZ regs) HS ltac:(vm_compute; reflexivity) Usp ltac:(lia)) as R2.
pose proof (fsw_reg_atom _ regs fs_extraT _ ms 3%bv 3%bv 3 HS ltac:(vm_compute; reflexivity) eq_refl) as R3.
pose proof (fsw_reg_atom _ regs fs_extraT _ ms 4%bv 4%bv 4 HS ltac:(vm_compute; reflexivity) eq_refl) as R4.
pose proof (fsw_reg_atom _ regs fs_extraT _ ms 8%bv 8%bv 8 HS ltac:(vm_compute; reflexivity) eq_refl) as R8.
destruct HSRC as (HZB & Hd4 & Hdc & Hdam & Hdra & Hdhull).
assert (U10 : bv_unsigned (ew E 10) = d).
{ subst E. rewrite (ew_Ereg_nat regs fs_extraT 10 10%bv eq_refl), H10. unfold w64. apply wz. lia. }
assert (U11 : bv_unsigned (ew E 11) = n).
{ subst E. rewrite (ew_Ereg_nat regs fs_extraT 11 11%bv eq_refl), H11. unfold w64. apply wz. lia. }
assert (U12 : bv_unsigned (ew E 12) = c).
{ subst E. rewrite (ew_Ereg_nat regs fs_extraT 12 12%bv eq_refl), H12. unfold w64. apply wz. lia. }
assert (U32 : bv_unsigned (ew E 32) = SHADOW_OFF).
{ subst E. change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. apply wz. unfold SHADOW_OFF. lia. }
pose proof (fsw_reg_off _ E _ ms 10%bv 11 18 n HS ltac:(vm_compute; reflexivity) U11 ltac:(lia)) as R10.
pose proof (fsw_reg_off _ E _ ms 9%bv 12 0 c HS ltac:(vm_compute; reflexivity) U12 ltac:(lia)) as R9.
pose proof (fsw_reg_off _ E _ ms 18%bv 10 0 d HS ltac:(vm_compute; reflexivity) U10 ltac:(lia)) as R18.
pose proof (fsw_reg_off _ E _ ms 19%bv 11 0 n HS ltac:(vm_compute; reflexivity) U11 ltac:(lia)) as R19.
pose proof (fsw_reg_off _ E _ ms 20%bv 32 0 SHADOW_OFF HS ltac:(vm_compute; reflexivity) U32 ltac:(unfold SHADOW_OFF; lia)) as R20.
rewrite Z.add_0_r in R9, R18, R19, R20.
assert (Hspc : spZ (ms_regs ms) = spZ regs + -64) by (unfold spZ at 1; rewrite R2; lia).
assert (RQ : forall q : nat, (q = 3 \/ q = 4 \/ 23 <= q <= 27)%nat ->
  getr (ms_regs ms) (Z_to_bv 5 (Z.of_nat q)) = getr regs (Z_to_bv 5 (Z.of_nat q))).
{ intros q Hq.
  assert (Hq' : q = 3%nat \/ q = 4%nat \/ q = 23%nat \/ q = 24%nat \/ q = 25%nat \/ q = 26%nat \/ q = 27%nat) by lia.
  destruct Hq' as [->|[->|[->|[->|[->|[->| ->]]]]]]; match goal with |- getr _ (Z_to_bv 5 (Z.of_nat ?k)) = _ =>
    apply (fsw_reg_atom _ regs fs_extraT _ ms _ _ k HS) end; vm_compute; reflexivity. }
assert (HCH : chain_pre ly (aview tfibsegs (w_H W) (unpoison U (ms_mem ms))) (ms_regs ms) ch).
{ apply (achain_chain_pre ly _ (spZ regs) (s0Z regs) ch (ms_regs ms)).
  - apply (achain_kept ly (aview tfibsegs (w_H W) (unpoison U mem)) _ (spZ regs) (s0Z regs) ch (spZ regs) Hch ltac:(lia)).
    + pose proof Hstk as (_ & _ & _ & _ & Hshi & Hshi47 & _ & _ & Htop2). lia.
    + intros a Ha. pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _). apply F1; lia.
  - lia.
  - unfold s0Z. rewrite R8. reflexivity.
  - unfold raZ. rewrite R1, unsigned_lit_small by (unfold RA_PN_MALLOC; lia). unfold RA_PN_MALLOC. lia. }
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E _ ms HS eq_refl). cbn [ss_pc]. change 340196 with PC_malloc. rewrite <- HMPC.
(* ---- the call of __wrap_malloc (n + 18): ALLOC's B kit step; C5 by its second disjunct (st_nev S < EV_MAX) ---- *)
eapply SRr_bind.
{ exact (fsw_aj_malloc04U (SK := SKB) B FS_ENV ML AMALLOC W (ms_regs ms) (ms_mem ms) STK_past_nul (spZ regs) [] ly S W mem md []
    ly S U (with_vm_backing (m_vm_lazy md) mat md) 0 (n + 18) (-64) (Z_to_bv 64 RA_PN_MALLOC) ch HJ HARU
    ltac:(unfold w64; rewrite <- R10; symmetry; apply Z_to_bv_bv_unsigned)
    ltac:(unfold MALLOC_MAX in *; lia) Hlv Hspc eq_refl ltac:(lia) ltac:(unfold ASTACK; lia)
    ltac:(rewrite R3; exact Hgp) ltac:(rewrite R4; exact Htp) R1
    ltac:(apply ret_ok_even; rewrite unsigned_lit_small by (unfold RA_PN_MALLOC; lia); reflexivity)
    ltac:(unfold EV_past_nul in Hev; lia) HCH). }
intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HARU2 & HJ2 & HP2 & H10r & Hfr2 & Hres & Hbl2 & HK2).
(* ---- back at 0x828d8 ---- *)
pose proof (fsw_region_nth E _ _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
pose proof (pn_frame_of_entry regs (w_H W) (ms_mem ms) (spZ regs) HR0 Usp) as PF1. clear HR0.
pose proof HK2 as (K1 & K2 & K3 & K4 & K5 & K6).
assert (HSA : forall a, spZ regs - 64 <= a < spZ regs ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W) (ms_mem ms) a).
{ intros a Ha.
  rewrite <- (fsw_aview_unpoison_high B ly2 S2 U W2 mem2 md2 a HARU2) by lia.
  rewrite <- (fsw_aview_unpoison_high B ly S U W (ms_mem ms) _ a HARU) by lia.
  apply K1; lia. }
pose proof (pn_frame_kept _ (w_H W2) _ mem2 _ regs PF1 HSA) as PF2.
assert (Esp2 : getr regs2 2 = getr (ms_regs ms) 2) by exact (HP2 2 ltac:(unfold acallee_saved; lia)).
assert (Usp2 : spZ regs2 = spZ regs - 64) by (unfold spZ at 1; rewrite Esp2; change (bv_unsigned (getr (ms_regs ms) 2)) with (spZ (ms_regs ms)); lia).
pose proof (fsw_resume_after_rtU_args_chunks (SK := SKB) B STK_past_nul (spZ regs) [] ly S W (unpoison U mem) md [] ly2 S2 U W2 mem2 md2 (0 + 1)
  regs2 64 (pn_xs regs) pn_cs [] [] RA_PN_MALLOC HGOT HCELL HJ2 HARU2 Usp2 ltac:(lia) ltac:(lia) eq_refl ltac:(vm_compute; reflexivity)
  (pn_frame_cs _ _ _ regs regs2 PF2) (Forall_nil _)) as HS2.
set (E2 := Ereg regs2 (fs_extraT ++ pn_xs regs)) in HS2.
assert (E2b : bv_unsigned (ew E2 2) = spZ regs - 64) by (subst E2; rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl); exact Usp2).
specialize (HS2 ltac:(apply pairwise_disjoint_of_extents;
  unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, extent_of_region;
  cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite E2b;
  unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address;
  cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd];
  repeat match goal with |- _ /\ _ => split end; try exact I; lia) I).
assert (E10 : ew E2 10 = Z_to_bv 64 res) by (subst E2; rewrite (ew_Ereg_nat regs2 _ 10 10%bv eq_refl); exact H10r).
fsw_aj_runU pn_tbl_ok HS2 HJ2 HARU2.
{ unfold fss_retT, fsT_ret_regions; cbn [ss_mem app].
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -64); pn_awr_side E2b.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch type of HS2 with st_ok _ _ _ (restrict _ ?mm) => rename mm into msA end.
pose proof (pn_blk_of ly S U W mem md n res ly2 S2 W2 _ _ ltac:(lia) HARU0 HARU2 Hbl2) as (_ & _ & _ & _ & Hresc & _).
(* `beqz a0` 0x828d8: the NULL arm (__asan_handle_no_return; abort) is untaken, t >= 4096 *)
apply (SRr_sym_branch tfibsegs W2 E2 _ msA _ _ BC_EQ (SOff 10 0) (SLit 0) HS2); intros Hb HS3;
  rewrite branch_eq_U, (U_atom _ 10 res E10 ltac:(lia)), U_lit in Hb by lia;
  lazymatch type of Hb with
  | _ = true => exfalso; apply Z.eqb_eq in Hb; lia
  | _ = false => clear Hb HS2
  end.
(* ---- the atoms of the post-malloc env E2 ---- *)
assert (VQ : forall q : nat, (q = 3 \/ q = 4 \/ 23 <= q <= 27)%nat -> ew E2 q = getr regs (Z_to_bv 5 (Z.of_nat q))).
{ intros q Hq. subst E2.
  assert (Hu : Z.of_nat q = bv_unsigned (Z_to_bv 5 (Z.of_nat q))) by (rewrite Z_to_bv_unsigned, bv_wrap_small; [lia|]; unfold bv_modulus; cbn; lia).
  rewrite (ew_Ereg_nat regs2 _ q _ Hu), (fsw_pres _ _ _ HP2) by (rewrite <- Hu; unfold acallee_saved; lia). exact (RQ q Hq). }
assert (G : forall (k : nat) (r : bv 5) v, Z.of_nat k = bv_unsigned r -> acallee_saved (bv_unsigned r) ->
  bv_unsigned (getr (ms_regs ms) r) = v -> 0 <= v < 2 ^ 64 -> ew E2 k = Z_to_bv 64 v).
{ intros k r v Hk Hr Hv Hv64. subst E2. rewrite (ew_Ereg_nat regs2 _ k r Hk), (fsw_pres _ _ r HP2 Hr).
  apply bv_eq. rewrite Hv, unsigned_lit_small by lia. lia. }
assert (V9 : ew E2 9 = Z_to_bv 64 c) by exact (G 9%nat 9%bv c eq_refl ltac:(pn_csv) R9 ltac:(lia)).
assert (V18 : ew E2 18 = Z_to_bv 64 d) by exact (G 18%nat 18%bv d eq_refl ltac:(pn_csv) R18 ltac:(lia)).
assert (V19 : ew E2 19 = Z_to_bv 64 n) by exact (G 19%nat 19%bv n eq_refl ltac:(pn_csv) R19 ltac:(lia)).
assert (V20 : ew E2 20 = Z_to_bv 64 SHADOW_OFF) by exact (G 20%nat 20%bv SHADOW_OFF eq_refl ltac:(pn_csv) R20 ltac:(unfold SHADOW_OFF; lia)).
assert (EX2 : forall j, (j < 9)%nat -> ew E2 (32 + j) = nth j (fs_extraT ++ pn_xs regs) (Z_to_bv 64 0)) by (intros j Hj; apply ew_Ereg_extra).
pose proof (garr8_bytes_ok tfibsegs _ _ _ HZB) as Hdb.
assert (Hsrc0 : forall i, 0 <= i < n -> aview tfibsegs (w_H W) mem (d + i) = Some (nth (Z.to_nat i) db 0)).
{ intros i Hi. replace (d + i) with (d + Z.of_nat (Z.to_nat i)) by lia. apply pn_aview_of_garr8; [exact HZB | lia]. }
(* `beqz s3` 0x828e0: n = 0 goes straight to the join, n > 0 calls __asan_memcpy *)
fsw_aj_runU pn_tbl_ok HS3 HJ2 HARU2.
{ unfold fss_retT, fsT_ret_regions; cbn [add_cond ss_mem app].
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -64); pn_awr_side E2b.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch type of HS3 with st_ok _ _ _ (restrict _ ?mm) => rename mm into msB end.
apply (SRr_sym_branch tfibsegs W2 E2 _ msB _ _ BC_EQ (SOff 19 0) (SLit 0) HS3); intros Hb HS4;
  rewrite branch_eq_U, (U_atom _ 19 n V19 ltac:(lia)), U_lit in Hb by lia; clear HS3.
all: lazymatch type of Hb with
  | _ = true => apply Z.eqb_eq in Hb
  | _ = false => apply Z.eqb_neq in Hb
  end.
- (* n = 0: on to the join *)
  fsw_aj_run_toU pn_tbl_ok HS4 HJ2 HARU2 PN_JOIN.
  { cbn [add_cond ss_mem].
    eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -64); pn_awr_side E2b.
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  lazymatch type of HS4 with st_ok _ _ _ (restrict _ ?mm) => rename mm into msJ end.
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W2) E2 _ msJ HS4 eq_refl). cbn [ss_pc]. change 534772 with PN_JOIN.
  eapply SRr_mono.
  { exact (pn_post ly S U W regs mem md n c db live peak cnt fail res ly2 S2 W2 (ms_regs msJ) (ms_mem msJ) _
      Hra FH HG Hc Hn Hlen Hdb HARU0 HJ2 HARU2 Hbl2
      ltac:(unfold spZ at 1; pn_sr HS4 (2%bv : bv 5); rewrite fsw_SOff0; exact E2b)
      ltac:(pn_sr HS4 (3%bv : bv 5); rewrite fsw_SOff0, (VQ 3%nat ltac:(lia)); exact Hgp)
      ltac:(pn_sr HS4 (4%bv : bv 5); rewrite fsw_SOff0, (VQ 4%nat ltac:(lia)); exact Htp)
      ltac:(pn_val HS4 (8%bv : bv 5) E2) ltac:(pn_val HS4 (9%bv : bv 5) E2)
      ltac:(pn_val HS4 (19%bv : bv 5) E2) ltac:(pn_val HS4 (20%bv : bv 5) E2)
      ltac:(pn_rcsv HS4 VQ)
      ltac:(pose proof (fsw_region_nth E2 _ _ 0 _ HS4 eq_refl) as HRf; cbn [ms_mem restrict] in HRf;
            exact (pn_frame_of_cs E2 _ _ _ regs _ EX2 E2b (fun c0 Hc0 => Hc0) HRf))
      ltac:(intros i Hi; lia)). }
  intros W' c' _ Hp. exact Hp.
- (* n > 0: the __asan_memcpy call 0x828f0 *)
  destruct (HBLK ltac:(lia)) as (b & m & Hbm & Hbd & Hdn).
  fsw_aj_runU pn_tbl_ok HS4 HJ2 HARU2.
  { cbn [add_cond ss_mem].
    eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -64); pn_awr_side E2b.
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  lazymatch type of HS4 with st_ok _ _ _ (restrict _ ?mm) => rename mm into msC end.
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W2) E2 _ msC HS4 eq_refl). cbn [ss_pc]. change 335248 with PC_memcpy.
  rewrite Hlen in Hdra, Hdam, Hdc.
  eapply SRr_mono.
  { exact (pn_mid ly S U W regs mem md n c db live peak cnt fail res ly2 S2 W2 (ms_regs msC) (ms_mem msC) _ d b m
      Hra FH HG Hc ltac:(lia) Hlen Hdb HARU0 Hdra Hdam Hd4 ltac:(lia) Hbm Hbd Hdn Hsrc0 HJ2 HARU2 Hbl2
      (fsw_reg_lit _ E2 _ msC 1%bv PN_JOIN HS4 ltac:(vm_compute; reflexivity) ltac:(unfold PN_JOIN; lia))
      ltac:(unfold spZ at 1; pn_sr HS4 (2%bv : bv 5); rewrite fsw_SOff0; exact E2b)
      ltac:(pn_sr HS4 (3%bv : bv 5); rewrite fsw_SOff0, (VQ 3%nat ltac:(lia)); exact Hgp)
      ltac:(pn_sr HS4 (4%bv : bv 5); rewrite fsw_SOff0, (VQ 4%nat ltac:(lia)); exact Htp)
      ltac:(pn_val HS4 (10%bv : bv 5) E2) ltac:(pn_val HS4 (11%bv : bv 5) E2) ltac:(pn_val HS4 (12%bv : bv 5) E2)
      ltac:(pn_val HS4 (8%bv : bv 5) E2) ltac:(pn_val HS4 (9%bv : bv 5) E2)
      ltac:(pn_val HS4 (19%bv : bv 5) E2) ltac:(pn_val HS4 (20%bv : bv 5) E2)
      ltac:(pn_rcsv HS4 VQ)
      ltac:(pose proof (fsw_region_nth E2 _ _ 0 _ HS4 eq_refl) as HRf; cbn [ms_mem restrict] in HRf;
            exact (pn_frame_of_cs E2 _ _ _ regs _ EX2 E2b (fun c0 Hc0 => Hc0) HRf))). }
  intros W' c' _ Hp. exact Hp.
Qed.

End W.

Set Printing Implicit.
About past_nul_ok.
Unset Printing Implicit.
Print Assumptions past_nul_ok.
