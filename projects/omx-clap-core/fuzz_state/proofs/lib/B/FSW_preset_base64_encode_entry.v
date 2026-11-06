(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths, module names and numbers changed; 1266 of its 1332 lines of code are new or changed and 1014 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_dec_E.v; 829 of its 913 lines of code are new or changed and 1248 lines of the source are left out. *)
(* preset_base64_encode 0x84700 (preset_file.c:577-608) on fs.asan-ubsan (image B), the ENTRY of the walk of
   lib/B/FSH_Fn_writer.v's encode_spec: the prologue and the size, the fuzz_malloc call, the refused allocation (null arm),
   the len < 3 dispatch, and the set-up of round 0 at the loop head.

   What it proves:
   - encE_spine: B 0x84700 (addi sp,sp,-48; the six saves 40(sp) .. 0(sp) of ra, s0, s1, s2, s3, s4; s0 = len; s1 = data;
     the shadow base s2 from the .got word 0x9fc10; the size a0 = enc_size len from the .rodata word 0x10320
     (`mulhu; slli 1; andi -4; addi 1`, encE_size_den)) to the call `jal fuzz_malloc` 0x8474c, the callee's fpreU,
     lib/B/FSH_Fn_alloc.v's fuzz_malloc_spec (Section hypothesis HMALLOC, CTX-free) at n = enc_size len, and the resumed
     state at the return 0x84750 in both of its arms (encE_res: the journal at the entry sp, ARU, the resumed symbolic
     state for any atom facts, the registers the rest of the walk reads);
   - encE_null: the refused arm, `beqz a0` 0x84750 taken, the epilogue 0x84b38 .. the `ret` 0x84b54: encode_spec's first
     disjunct (journal count 0, U unchanged);
   - encE_at: from the call's post to every hypothesis of lib/B/FSW_preset_base64_encode_R.v's Section R (encE_Rhyps:
     HLN HBS HBSL HDLO HDHI HARUc HHEADS HQB HAB HQ16 HDB HRBc HGLOBc HTABc HRATc HDATc HKEEPc HFRAMEc HSP0 HRA0) and
     encR_inv, at the memory where the walk hands over;
   - encE_succ: the granted arm: `beqz a0` not taken, a4 := g_b64 0x84758 / 0x8475c, `bltu s0,a1` 0x84760 with a1 = 3:
     * len = 0: 0x849a0 a3 := 0, a1 := a0, `bltu zero,s0` 0x849a8 not taken, `j` 0x849ac to the NUL 0x84b24, where
       Section R's encR_nul ends the walk;
     * len in {1, 2}: 0x849a8 taken, the tail entry 0x849bc with encR_exit_regs ms 0 (continuation encE_KTAIL, the shape
       of the tail lane's encR_tail_entry_nul at R = 0);
     * 3 <= len: 0x84764 .. 0x84784 (a6 := not data, a7 := data + 1, a5 := 2, t0 := snez data = 1, t1 := not g_b64,
       t2 := -1, a1 := t6 := a0, `add a2,s1,a5`), the loop head 0x84788 with encR_loop_regs ms 0 (continuation
       encE_KLOOP, the shape of lib/B/FSW_preset_base64_encode_loop.v's encR_loop at r = 0);
   - encE_entry / encE_encode_spec: encode_spec from the two continuations.
   No UBSan decider (a branch to 0x84b58) and no ASan report branch lies in 0x84700 .. 0x84784 or on the len < 3 landing
   0x849a0 .. 0x849ac: the first UBSan decider is 0x8478c (the round lane's), the first shadow check 0x847a4. The runs
   here are plain engine runs (no shadow load: the .got word, the shadow-base cell and the .rodata word are regions).

   rule 24: proves function preset_base64_encode (part entry; reuse search: proof-index preset_base64_encode,
   ported from a working branch 402eb5565fc + donor a working branch b96980d72d1)
   Port-from: A's entry walk is not written at 402eb5565fc (lib/A/FSW_preset_base64_encode.v has no entry piece); the
   form of the spine / null arm / call step is lib/A/FSW_dec_E.v on the base a9edd281227 (decE_spine 1087-1459, decE_null
   344-490, decE_cs_den / decE_chunks_of_frame 74-122) and lib/B/FSW_parse_string.v (pstr_call_post 949-1083, the
   live-block keep through the journal); the image-B steps from the old-B donor a working branch b96980d72d1
   lib/B/Prog/preset_base64_encode_blocks.v:54-95 (enc_prologue: frame 48, six saves, the size), 105-148
   (enc_epilogue / enc_body_null), 1266-1285 (enc_body_B: the malloc test, the len < 3 and len = 0 dispatch, the
   round-0 set-up). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
FSupoison FSupoisonU FSH_YC20 FSH_Gen FSW_preset_base64_encode_blocks.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSPstat FSH_Fn_writer FSH_Fn_alloc FSW_K FSW_K3 FSW_rres FSW_ret FSW_writer_tbl
FSW_preset_base64_encode_W FSW_preset_base64_encode_R FSW_preset_base64_encode_loop.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require FSW_preset_base64_encode_ub FSW_rd.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ---- the pcs of the walk: the call's return, the loop head, the tail entry, the NUL store ---- *)
Definition ENC_RA_MALLOC : Z := 0x84750.
Definition ENC_HEAD : Z := 0x84788.
Definition ENC_TAIL : Z := 0x849bc.
Definition ENC_NUL : Z := 0x84b24.
(* the resumed state after fuzz_malloc: the 48-byte frame at atom 2 = sp - 48; the four saved registers the code has
   changed by the call (ra, s0 = len, s1 = data, s2 = the shadow base) are extra atoms 33 .. 36 (xatom 0 .. 3), s3 / s4
   (untouched) are the resumed registers' own atoms *)
Definition encE_xs (regs : bvmap 5 word) : list word := [getr regs 1; getr regs 8; getr regs 9; getr regs 18].
Definition encE_cs : list YP09.chunk :=
  [YP09.mkChunk 40 (CVal 8 (SOff 33 0)); YP09.mkChunk 32 (CVal 8 (SOff 34 0));
   YP09.mkChunk 24 (CVal 8 (SOff 35 0)); YP09.mkChunk 16 (CVal 8 (SOff 36 0));
   YP09.mkChunk 8 (CVal 8 (SOff 19 0)); YP09.mkChunk 0 (CVal 8 (SOff 20 0))].
(* the a0 the engine leaves at the call: ((s0 + 2) mulhu 0xaaaaaaaaaaaaaaab) << 1 & -4 + 1 (B 0x84734 .. 0x84748) *)
Definition encE_size_sv : sv :=
  SAlu ALU_ADD (SAlu ALU_AND (SAlu ALU_SLL (SMd M_MULHU (SOff 11 2) (SLit 12297829382473034411)) (SLit 1))
    (SLit (-4))) (SLit 1).
(* the atom facts of the granted arm's resumed state: s0 = len in [lo, hi] (decides `bltu s0,a1` 0x84760 and
   `bltu zero,s0` 0x849a8), s1 = data, a0 = q (decides `beqz a0` 0x84750) *)
Definition encE_gf (lo hi : Z) : list (nat * afact) :=
  [(8%nat, mkAF lo hi 0); (9%nat, mkAF 4096 PTOP 0); (10%nat, mkAF 4112 PTOP 0)].
(* the callee-saved registers the walk leaves alone up to the call (s3 / s4 are saved but not changed) *)
Definition encE_zs : list Z := [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27].

Ltac encE_cs_side := unfold acallee_saved; lazymatch goal with |- context [bv_unsigned ?q] =>
  let z := eval vm_compute in (bv_unsigned q) in change (bv_unsigned q) with z end; lia.

(* ---- the size: what the five instructions leave in a0 is enc_size len (the model half's enc_machine) ---- *)
Lemma encE_size_den : forall E len, ew E 11 = w64 len -> 0 <= len <= 2 ^ 27 ->
  sv_denot E encE_size_sv = w64 (enc_size len).
Proof.
intros E len H11 Hl. rewrite denot_lit_U. unfold w64. f_equal.
assert (HQ : 0 <= 2 * (len + 2) / 3 <= 2 ^ 28)
  by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (HQ3 : 0 <= (len + 2) / 3 <= 2 ^ 27)
  by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (U0 : U E (SOff 11 2) = len + 2) by (apply (U_atom_off E 11 len 2); [exact H11 | lia | lia]).
assert (U1 : U E (SMd M_MULHU (SOff 11 2) (SLit 12297829382473034411)) = 2 * (len + 2) / 3).
{ rewrite U_SMd. cbn [zmd_raw]. rewrite U0, U_SLit.
  change (zcanon 12297829382473034411) with ENC_MAGIC. change (Z.of_N 64) with 64.
  rewrite enc_mulhu by lia. apply zcanon_id. unfold M64. lia. }
assert (U2 : U E (SAlu ALU_SLL (SMd M_MULHU (SOff 11 2) (SLit 12297829382473034411)) (SLit 1))
             = 2 * (len + 2) / 3 * 2).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite U1, U_SLit. change (Z.land (zcanon 1) 63) with 1.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. apply zcanon_id. unfold M64. lia. }
assert (U3 : U E (SAlu ALU_AND (SAlu ALU_SLL (SMd M_MULHU (SOff 11 2) (SLit 12297829382473034411)) (SLit 1))
                (SLit (-4))) = (len + 2) / 3 * 4).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite U2, U_SLit. change (zcanon (-4)) with (2 ^ 64 - 4).
  rewrite land_m4 by lia. rewrite (enc_q4 len) by lia. rewrite zcanon_id by (unfold M64; lia). lia. }
unfold encE_size_sv. rewrite U_SAlu. cbn [zalu_raw]. rewrite U3, U_SLit. change (zcanon 1) with 1.
unfold enc_size. apply zcanon_id. unfold M64. lia.
Qed.

(* ---- small image facts of fs.asan-ubsan (the twins of FSW_strdup.v's sd_ro_not_pstat and of the A walks'
   pstat lemmas): fuzz/alloc.c's four statics are image bytes, none of them read-only, and the sink is closed ---- *)
Lemma encE_ro_not_pstat : forall a, in_roP tfibsegs FS_RLO FS_RHI a -> ~ inFP FS_PSTAT_FP a.
Proof.
intros a Hro (r & Hr & Ha).
assert (Hb : forallb (fun r : Z * Z => (FS_RHI <=? fst r) &&
  forallb (fun s => seg_writable s || (snd r <=? Z.of_N (seg_base s)) ||
                    (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? fst r)) tfibsegs) FS_PSTAT_FP = true)
  by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) Hb r Hr) as H. cbv beta in H. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1.
destruct Hro as [(sg & Hsg & Hw & Hs) | Hrl]; [|lia].
pose proof (proj1 (forallb_forall _ _) H2 sg Hsg) as H3. cbv beta in H3. rewrite Hw in H3. cbn [orb] in H3.
apply orb_prop in H3 as [H3|H3]; apply Z.leb_le in H3; lia.
Qed.
Lemma encE_pstat_closed : ~ YI16.sink_open_fp FS_PSTAT_FP.
Proof. apply sink_closed_pos. unfold FS_PSTAT_FP. repeat (apply Forall_cons; [cbn [fst]; lia|]). apply Forall_nil. Qed.

(* ---- the six saved cells: the entry ra, s0, s1, s2, s3, s4 at sp0 - 8 .. sp0 - 48 (Section R's HFRAMEc) ---- *)
Definition encE_frame (W : world tfibsegs) (m : word -> option byte) (regs0 : bvmap 5 word) : Prop :=
  val_mem tfibsegs (mrestrict (w_H W) m) (spZ regs0 - 8) 8 (bv_unsigned (getr regs0 1)) /\
  val_mem tfibsegs (mrestrict (w_H W) m) (spZ regs0 - 16) 8 (bv_unsigned (getr regs0 8)) /\
  val_mem tfibsegs (mrestrict (w_H W) m) (spZ regs0 - 24) 8 (bv_unsigned (getr regs0 9)) /\
  val_mem tfibsegs (mrestrict (w_H W) m) (spZ regs0 - 32) 8 (bv_unsigned (getr regs0 18)) /\
  val_mem tfibsegs (mrestrict (w_H W) m) (spZ regs0 - 40) 8 (bv_unsigned (getr regs0 19)) /\
  val_mem tfibsegs (mrestrict (w_H W) m) (spZ regs0 - 48) 8 (bv_unsigned (getr regs0 20)).

(* one 8-byte chunk of a stack region, as a value in memory *)
Lemma encE_cell : forall E m n b lo hi wlo whi cs od e v,
  region_ok tfibsegs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal 8 e)) cs -> sv_denot E e = Z_to_bv 64 v ->
  0 <= v < 2 ^ 64 -> val_mem tfibsegs m (b + od) 8 v.
Proof.
intros E m n b lo hi wlo whi cs od e v HR Hb Hc He Hv.
exact (fsw_field E m n b cs lo hi wlo whi od 8%N e v HR Hb Hc He Hv ltac:(cbn [Z.of_N]; lia)).
Qed.

(* the prologue's frame (the engine's stack region at the call, offsets from the entry sp) *)
Lemma encE_frame_of_call : forall (W : world tfibsegs) m regs,
  region_ok tfibsegs (Ereg regs fs_extraT) (mrestrict (w_H W) m)
    (YP09.mkRegion (Some 2%nat) (-48) 0 (-48) 0
       [YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0));
        YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0));
        YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))]) ->
  encE_frame W m regs.
Proof.
intros W m regs HR.
assert (E2 : bv_unsigned (ew (Ereg regs fs_extraT) 2) = spZ regs)
  by (rewrite (ew_Ereg_nat regs fs_extraT 2 2%bv eq_refl); reflexivity).
assert (F : forall od (r : bv 5) n, Z.of_nat n = bv_unsigned r ->
  In (YP09.mkChunk od (CVal 8 (SOff n 0)))
    [YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0));
     YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0));
     YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))] ->
  val_mem tfibsegs (mrestrict (w_H W) m) (spZ regs + od) 8 (bv_unsigned (getr regs r))).
{ intros od r n Hn Hin. apply (encE_cell _ _ 2 _ _ _ _ _ _ od (SOff n 0) _ HR E2 Hin); [|apply u64_range].
  rewrite fsw_SOff0, (ew_Ereg_nat regs fs_extraT n r Hn). symmetry. apply Z_to_bv_bv_unsigned. }
unfold encE_frame.
split; [replace (spZ regs - 8) with (spZ regs + -8) by lia; apply (F (-8) 1%bv 1%nat); [reflexivity | cbn; tauto]|].
split; [replace (spZ regs - 16) with (spZ regs + -16) by lia; apply (F (-16) 8%bv 8%nat); [reflexivity | cbn; tauto]|].
split; [replace (spZ regs - 24) with (spZ regs + -24) by lia; apply (F (-24) 9%bv 9%nat); [reflexivity | cbn; tauto]|].
split; [replace (spZ regs - 32) with (spZ regs + -32) by lia; apply (F (-32) 18%bv 18%nat); [reflexivity | cbn; tauto]|].
split; [replace (spZ regs - 40) with (spZ regs + -40) by lia; apply (F (-40) 19%bv 19%nat); [reflexivity | cbn; tauto]|].
replace (spZ regs - 48) with (spZ regs + -48) by lia; apply (F (-48) 20%bv 20%nat); [reflexivity | cbn; tauto].
Qed.

(* the resumed state's frame region (offsets from sp0 - 48), read back as the six cells *)
Lemma encE_frame_of_ret : forall (W : world tfibsegs) m regs regs',
  getr regs' 19 = getr regs 19 -> getr regs' 20 = getr regs 20 ->
  bv_unsigned (ew (Ereg regs' (fs_extraT ++ encE_xs regs)) 2) = spZ regs - 48 ->
  region_ok tfibsegs (Ereg regs' (fs_extraT ++ encE_xs regs)) (mrestrict (w_H W) m) (fstk_ret 48 encE_cs) ->
  encE_frame W m regs.
Proof.
intros W m regs regs' G19 G20 E2 HR. unfold fstk_ret in HR.
assert (F : forall od e v, In (YP09.mkChunk od (CVal 8 e)) encE_cs ->
  sv_denot (Ereg regs' (fs_extraT ++ encE_xs regs)) e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  val_mem tfibsegs (mrestrict (w_H W) m) (spZ regs - 48 + od) 8 v)
  by (intros od e v Hin He Hv; exact (encE_cell _ _ 2 _ _ _ _ _ _ od e v HR E2 Hin He Hv)).
assert (X : forall j (r : bv 5), nth j (encE_xs regs) (Z_to_bv 64 0) = getr regs r ->
  sv_denot (Ereg regs' (fs_extraT ++ encE_xs regs)) (SOff (33 + j) 0) = Z_to_bv 64 (bv_unsigned (getr regs r))).
{ intros j r Hj. rewrite fsw_SOff0. change (33 + j)%nat with (32 + S j)%nat. rewrite ew_Ereg_extra.
  cbn [fs_extraT app nth]. rewrite Hj. symmetry. apply Z_to_bv_bv_unsigned. }
unfold encE_frame.
split; [replace (spZ regs - 8) with (spZ regs - 48 + 40) by lia;
        apply (F 40 (SOff 33 0)); [cbv [encE_cs In]; tauto | exact (X 0%nat 1%bv eq_refl) | apply u64_range]|].
split; [replace (spZ regs - 16) with (spZ regs - 48 + 32) by lia;
        apply (F 32 (SOff 34 0)); [cbv [encE_cs In]; tauto | exact (X 1%nat 8%bv eq_refl) | apply u64_range]|].
split; [replace (spZ regs - 24) with (spZ regs - 48 + 24) by lia;
        apply (F 24 (SOff 35 0)); [cbv [encE_cs In]; tauto | exact (X 2%nat 9%bv eq_refl) | apply u64_range]|].
split; [replace (spZ regs - 32) with (spZ regs - 48 + 16) by lia;
        apply (F 16 (SOff 36 0)); [cbv [encE_cs In]; tauto | exact (X 3%nat 18%bv eq_refl) | apply u64_range]|].
split; [replace (spZ regs - 40) with (spZ regs - 48 + 8) by lia;
        apply (F 8 (SOff 19 0)); [cbv [encE_cs In]; tauto | | apply u64_range];
        rewrite fsw_SOff0, (ew_Ereg_nat regs' _ 19 19%bv eq_refl), G19; symmetry; apply Z_to_bv_bv_unsigned|].
replace (spZ regs - 48) with (spZ regs - 48 + 0) at 1 by lia.
apply (F 0 (SOff 20 0)); [cbv [encE_cs In]; tauto | | apply u64_range].
rewrite fsw_SOff0, (ew_Ereg_nat regs' _ 20 20%bv eq_refl), G20. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* the six cells at the call's memory, as the resumed state's frame chunks *)
Lemma encE_cs_ok : forall (W : world tfibsegs) m regs regs',
  getr regs' 19 = getr regs 19 -> getr regs' 20 = getr regs 20 -> encE_frame W m regs ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs' (fs_extraT ++ encE_xs regs)) (mrestrict (w_H W) m) (spZ regs - 48))
    encE_cs.
Proof.
intros W m regs regs' G19 G20 (V1 & V8 & V9 & V18 & V19 & V20).
assert (C : forall od e (r : bv 5),
  sv_denot (Ereg regs' (fs_extraT ++ encE_xs regs)) e = getr regs r ->
  val_mem tfibsegs (mrestrict (w_H W) m) (spZ regs - 48 + od) 8 (bv_unsigned (getr regs r)) ->
  YP09.chunk_ok tfibsegs (Ereg regs' (fs_extraT ++ encE_xs regs)) (mrestrict (w_H W) m) (spZ regs - 48)
    (YP09.mkChunk od (CVal 8 e))).
{ intros od e r He Hv. apply (chunk_ok_val tfibsegs _ _ _ od 8 e (bv_unsigned (getr regs r)));
    [rewrite He; symmetry; apply Z_to_bv_bv_unsigned | apply u64_range | cbn [Z.of_N]; lia | exact Hv]. }
assert (XT : forall j (r : bv 5), nth j (encE_xs regs) (Z_to_bv 64 0) = getr regs r ->
  sv_denot (Ereg regs' (fs_extraT ++ encE_xs regs)) (SOff (33 + j) 0) = getr regs r).
{ intros j r Hj. rewrite fsw_SOff0. change (33 + j)%nat with (32 + S j)%nat. rewrite ew_Ereg_extra.
  cbn [fs_extraT app nth]. exact Hj. }
unfold encE_cs. repeat apply Forall_cons; [..|apply Forall_nil].
- apply (C 40 _ 1%bv (XT 0%nat 1%bv eq_refl)). replace (spZ regs - 48 + 40) with (spZ regs - 8) by lia. exact V1.
- apply (C 32 _ 8%bv (XT 1%nat 8%bv eq_refl)). replace (spZ regs - 48 + 32) with (spZ regs - 16) by lia. exact V8.
- apply (C 24 _ 9%bv (XT 2%nat 9%bv eq_refl)). replace (spZ regs - 48 + 24) with (spZ regs - 24) by lia. exact V9.
- apply (C 16 _ 18%bv (XT 3%nat 18%bv eq_refl)). replace (spZ regs - 48 + 16) with (spZ regs - 32) by lia. exact V18.
- apply (C 8 _ 19%bv); [rewrite fsw_SOff0, (ew_Ereg_nat regs' _ 19 19%bv eq_refl); exact G19|].
  replace (spZ regs - 48 + 8) with (spZ regs - 40) by lia. exact V19.
- apply (C 0 _ 20%bv); [rewrite fsw_SOff0, (ew_Ereg_nat regs' _ 20 20%bv eq_refl); exact G20|].
  replace (spZ regs - 48 + 0) with (spZ regs - 48) by lia. exact V20.
Qed.

(* a register the engine left as its own atom, for a list of registers checked by computation *)
Section K. Context {fx : YK11.FPState}.
Lemma encE_kept_gen : forall (H : word -> bool) regs0 extra ss ms (zs : list Z),
  st_ok tfibsegs (Ereg regs0 extra) ss (restrict H ms) ->
  forallb (fun z => sv_eqb (sr_get (ss_regs ss) (Z_to_bv 5 z)) (SOff (Z.to_nat z) 0)) zs = true ->
  forall z, In z zs -> 0 <= z < 32 -> getr (ms_regs ms) (Z_to_bv 5 z) = getr regs0 (Z_to_bv 5 z).
Proof.
intros H regs0 extra ss ms zs HS Hb z Hin Hz.
pose proof (proj1 (forallb_forall _ _) Hb z Hin) as Hq. cbv beta in Hq. apply sv_eqb_eq in Hq.
rewrite (st_ok_restrict_reg tfibsegs H _ ss ms _ HS), Hq, fsw_SOff0.
apply ew_Ereg_nat. rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 5) with 32; lia). lia.
Qed.
End K.
Lemma encE_zs_in : forall z, acallee_saved z -> z <> 2 -> z <> 8 -> z <> 9 -> z <> 18 -> In z encE_zs /\ 0 <= z < 32.
Proof. intros z Hz H2 H8 H9 H18. unfold acallee_saved in Hz. unfold encE_zs. cbn [In]. lia. Qed.

(* ================================================================================================================ *)
Section E. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* the shadow-cell pair (lib/B/FSH_Base.v FsShadowSyms) and the image facts (lib/B/FSH_Rt.v fs_img_facts), as in
   lib/B/FSW_preset_base64_encode_W.v's Section W *)
Hypothesis HSS : FsShadowSyms B.
Hypothesis IMG : fs_img_facts tfibsegs B.

(* the image layer of lib/B/FSW_preset_base64_encode_W.v at this section's B / HSS / IMG (as Section R's local copies) *)
Local Ltac encW X := first [exact (X B HSS IMG) | exact (X B IMG) | exact (X B HSS) | exact (X B) | exact X].
Let enc_blk_bounds := ltac:(encW FSW_preset_base64_encode_W.enc_blk_bounds).
Let enc_table := ltac:(encW FSW_preset_base64_encode_W.enc_table).
Let enc_magic_val := ltac:(encW FSW_preset_base64_encode_W.enc_magic_val).
Let enc_unp_apart := ltac:(encW FSW_preset_base64_encode_W.enc_unp_apart).
Let enc_img_rng := ltac:(encW FSW_preset_base64_encode_W.enc_img_rng).

Lemma encE_pstat_img : forall a, inFP FS_PSTAT_FP a -> in_img tfibsegs a.
Proof.
intros a (r & Hr & Ha). apply enc_img_rng. unfold FS_PSTAT_FP in Hr.
destruct Hr as [<- | [<- | [<- | [<- | []]]]]; cbn [fst snd] in Ha; lia.
Qed.

(* the read-only view on the unpoisoned memory: read-only bytes are image bytes, below the shadow band *)
Lemma encE_aro_unp : forall ly S U (W : world tfibsegs) mem md, ARU tfibsegs B ly S U W mem md ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) mem) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) (unpoison U mem)).
Proof.
intros ly S U W mem md HARU HR a Ha Ho He.
pose proof (FSW_rd.fsw_roP_img a Ha) as Hi. pose proof (fs_segs_img a Hi) as Hl.
assert (A64 : 0 <= a < 2 ^ 64) by (unfold FS_IMG_END in Hl; lia).
assert (NS : ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44)) by (unfold FS_IMG_END, SHADOW_OFF in *; lia).
rewrite (aview_at tfibsegs (w_H W) (unpoison U mem) mem a (FSW_rd.fsw_unpoison_app B ly S U W mem md a HARU A64 NS)).
exact (HR a Ha Ho He).
Qed.

(* the input block's bytes across the walk's journal: a live entry block, outside FS_PSTAT_FP (image bytes), kept by
   the journal's live-block clause; neither end's unpoison touches them (they lie off the shadow band) *)
Lemma encE_keep : forall ly S U (W : world tfibsegs) mem md ly' S' U' (W' : world tfibsegs) mem' md' k sp0 data len kd X,
  ajournal tfibsegs B STK_preset_base64_encode sp0 FS_PSTAT_FP ly S W (unpoison U mem) md []
    ly' S' W' (unpoison U' mem') md' k ->
  ARU tfibsegs B ly S U W mem md -> ARU tfibsegs B ly' S' U' W' mem' md' ->
  ablocks B ly' S' = ablocks B ly S ++ X ->
  (0 < len -> In (data - HEAD, kd + HEAD) (ablocks B ly S) /\ len <= kd /\ 0 < kd) ->
  forall i, 0 <= i < len ->
  mbyte tfibsegs (mrestrict (w_H W') mem') (data + i) = mbyte tfibsegs (mrestrict (w_H W) mem) (data + i).
Proof.
intros ly S U W mem md ly' S' U' W' mem' md' k sp0 data len kd X HJ HA HA' HX HDB i Hi.
destruct (HDB ltac:(lia)) as (Hin & Hkd & Hkd0).
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & J10 & _).
pose proof (ARU_AR tfibsegs B ly S U W mem md HA) as HAR.
assert (Hrq : req_size (kd + HEAD) = kd + HEAD)
  by (unfold req_size; destruct (kd + HEAD =? 0) eqn:E; [apply Z.eqb_eq in E; unfold HEAD in *; lia | reflexivity]).
assert (Hin' : In (data - HEAD, kd + HEAD) (ablocks B ly' S')) by (rewrite HX; apply in_or_app; left; exact Hin).
assert (Hr : data - HEAD <= data + i < data - HEAD + req_size (kd + HEAD)) by (rewrite Hrq; unfold HEAD; lia).
destruct (enc_blk_bounds ly S W (unpoison U mem) md (data - HEAD) (kd + HEAD) (data + i) HAR Hin Hr)
  as (B1 & B2 & B3).
assert (NF : ~ inFP FS_PSTAT_FP (data + i))
  by (intros Hf; exact (blk_img tfibsegs B LAWS ly S W (unpoison U mem) md _ _ (data + i) HAR Hin Hr
                          (encE_pstat_img _ Hf))).
assert (A64 : 0 <= data + i < 2 ^ 64) by lia.
assert (NS : ~ (SHADOW_OFF <= data + i < kHighMemBeg)) by (unfold kHighMemBeg, SHADOW_OFF in *; lia).
apply (mbyte_of_aview tfibsegs).
rewrite <- (aview_at tfibsegs (w_H W') (unpoison U' mem') mem' (data + i)
  (enc_unp_apart ly' S' U' W' mem' md' (data + i) HA' A64 NS)).
rewrite <- (aview_at tfibsegs (w_H W) (unpoison U mem) mem (data + i)
  (enc_unp_apart ly S U W mem md (data + i) HA A64 NS)).
replace (data + i) with (data - HEAD + (HEAD + i)) by lia.
apply (J10 (data - HEAD) (kd + HEAD) (HEAD + i) Hin Hin'); [rewrite Hrq; unfold HEAD; lia|].
replace (data - HEAD + (HEAD + i)) with (data + i) by lia. exact NF.
Qed.

(* ---- Section R's hypotheses (lib/B/FSW_preset_base64_encode_R.v lines 87-312, the same order), at the pre-call
   state (ly0 St0 U0 W0 mem0 regs0) and the state where the walk hands over (lyc Sc Wc memc mdc) ---- *)
Definition encE_Rhyps (ly0 : alayout) (St0 : astate) (U0 : list (Z * Z)) (W0 : world tfibsegs)
    (mem0 : word -> option byte) (regs0 : bvmap 5 word) (lyc : alayout) (Sc : astate) (Wc : world tfibsegs)
    (memc : word -> option byte) (mdc : Model) (data len q live peak cnt fail kd : Z) (bs : list Z) : Prop :=
  (0 <= len <= 2 ^ 27) /\ WriterSpec.bytes_ok bs /\ Z.of_nat (length bs) = len /\ 4096 <= data /\
  data + len <= alloc_ceiling /\
  ARU tfibsegs B lyc Sc (U0 ++ [(q - HEAD, HEAD)]) Wc memc mdc /\
  fs_heads B lyc Sc (U0 ++ [(q - HEAD, HEAD)]) /\
  In (q - HEAD, enc_size len + HEAD) (ablocks B lyc Sc) /\
  ablocks B lyc Sc = ablocks B ly0 St0 ++ [(q - HEAD, enc_size len + HEAD)] /\
  4096 + HEAD <= q /\
  (0 < len -> In (data - HEAD, kd + HEAD) (ablocks B ly0 St0) /\ len <= kd /\ 0 < kd) /\
  fs_rblock tfibsegs B lyc Sc Wc memc q (enc_size len) /\
  fs_glob tfibsegs Wc memc (live + enc_size len) (Z.max peak (live + enc_size len)) ((cnt + 1) mod 2 ^ 64) fail /\
  (forall v, 0 <= v < 64 -> val_mem tfibsegs (mrestrict (w_H Wc) memc) (G_B64 + v) 1 (WriterSpec.b64c v)) /\
  range_addressable (aview tfibsegs (w_H Wc) memc) SHADOW_OFF G_B64 65 /\
  garr8 tfibsegs (mrestrict (w_H Wc) memc) data bs /\
  (forall i, 0 <= i < len ->
     mbyte tfibsegs (mrestrict (w_H Wc) memc) (data + i) = mbyte tfibsegs (mrestrict (w_H W0) mem0) (data + i)) /\
  encE_frame Wc memc regs0 /\
  (spZ regs0 mod 16 = 0 /\ alloc_ceiling + STK_preset_base64_encode <= spZ regs0 /\ spZ regs0 <= 2 ^ 47) /\
  YK0s.ret_ok (getr regs0 1).

(* encode_spec's post (lib/B/FSH_Fn_writer.v lines 527-546, at segs = tfibsegs) *)
Definition encE_post (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) (data len : Z) (bs : list Z) (live peak cnt fail : Z)
    : world tfibsegs -> config -> Prop :=
  fun W' c' =>
    (cnt = fail /\
     fpostU tfibsegs B STK_preset_base64_encode (spZ regs) FS_PSTAT_FP regs ly S U W mem md 0 U
       (fun ly' S' W' regs' mem' md' =>
          getr regs' 10 = w64 0 /\
          ablocks B ly' S' = ablocks B ly S /\
          fs_glob tfibsegs W' mem' live peak ((cnt + 1) mod 2 ^ 64) SIZE_MAXZ) W' c')
    \/
    (exists q, cnt <> fail /\ q <> 0 /\
     fpostU tfibsegs B STK_preset_base64_encode (spZ regs) FS_PSTAT_FP regs ly S U W mem md
       EV_preset_base64_encode (U ++ [(q - HEAD, HEAD)])
       (fun ly' S' W' regs' mem' md' =>
          getr regs' 10 = w64 q /\ 4096 + HEAD <= q /\
          ablocks B ly' S' = ablocks B ly S ++ [(q - HEAD, enc_size len + HEAD)] /\
          fs_rblock tfibsegs B ly' S' W' mem' q (enc_size len) /\
          zbytes_at tfibsegs W' mem' q (WriterSpec.b64_enc bs ++ [0]) /\
          (forall i, 0 <= i < len ->
             mbyte tfibsegs (mrestrict (w_H W') mem') (data + i) = mbyte tfibsegs (mrestrict (w_H W) mem) (data + i)) /\
          fs_glob tfibsegs W' mem' (live + enc_size len)
            (Z.max peak (live + enc_size len)) ((cnt + 1) mod 2 ^ 64) fail) W' c').

(* ---- the two continuations: Section R's hypotheses at the hand-over state (memc = its memory, mdc = its model),
   then encR_loop's premises at r = 0 (lib/B/FSW_preset_base64_encode_loop.v lines 612-623) for 3 <= len, and the tail
   lane's encR_tail_entry_nul premises at R = 0 for len in {1, 2}; both end in encode_spec's success fpostU ---- *)
Definition encE_KLOOP (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) (data len : Z) (bs : list Z) (live peak cnt fail : Z) : Prop :=
  forall lyc Sc Wc q kd (ms : machine_state) md',
  encE_Rhyps ly S U W mem regs lyc Sc Wc (ms_mem ms) md' data len q live peak cnt fail kd bs ->
  0 <= 0 -> 3 * 0 + 3 <= len ->
  encR_inv B ly S U W mem md regs lyc Sc Wc (ms_mem ms) len q (ms_mem ms) md' ->
  encR_loop_regs regs data len q ms 0 ->
  garr8 tfibsegs (mrestrict (w_H Wc) (ms_mem ms)) q (WriterSpec.b64_enc (firstn (Z.to_nat (3 * 0)) bs)) ->
  SRr tfibsegs Wc (mkCfg (mkst (ms_regs ms) (w64 0x84788) (ms_mem ms) (seg_rom tfibsegs)) md')
    (fpostU tfibsegs B STK_preset_base64_encode (spZ regs) FS_PSTAT_FP regs ly S U W mem md
       EV_preset_base64_encode (U ++ [(q - HEAD, HEAD)]) (encR_Q B ly S W mem data len q live peak cnt fail bs)).
Definition encE_KTAIL (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) (data len : Z) (bs : list Z) (live peak cnt fail : Z) : Prop :=
  forall lyc Sc Wc q kd (ms : machine_state) md',
  encE_Rhyps ly S U W mem regs lyc Sc Wc (ms_mem ms) md' data len q live peak cnt fail kd bs ->
  0 <= 0 -> 3 * 0 < len -> len <= 3 * 0 + 2 ->
  encR_inv B ly S U W mem md regs lyc Sc Wc (ms_mem ms) len q (ms_mem ms) md' ->
  encR_exit_regs regs data len q ms 0 ->
  ms = mkst (ms_regs ms) (w64 0x849bc) (ms_mem ms) (seg_rom tfibsegs) ->
  garr8 tfibsegs (mrestrict (w_H Wc) (ms_mem ms)) q (WriterSpec.b64_enc (firstn (Z.to_nat (3 * 0)) bs)) ->
  SRr tfibsegs Wc (mkCfg ms md')
    (fpostU tfibsegs B STK_preset_base64_encode (spZ regs) FS_PSTAT_FP regs ly S U W mem md
       EV_preset_base64_encode (U ++ [(q - HEAD, HEAD)]) (encR_Q B ly S W mem data len q live peak cnt fail bs)).

(* ---- the state right after fuzz_malloc returned, at 0x84750 (both arms): the journal at the entry sp, ARU, the
   resumed symbolic state for any atom facts gf, and the registers the rest of the walk reads ---- *)
Definition encE_res (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) (W' : world tfibsegs) (ly' : alayout) (S' : astate)
    (U' : list (Z * Z)) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (k : Z) : Prop :=
  ajournal tfibsegs B STK_preset_base64_encode (spZ regs) FS_PSTAT_FP ly S W (unpoison U mem) md []
    ly' S' W' (unpoison U' mem') md' k /\
  ARU tfibsegs B ly' S' U' W' mem' md' /\
  (forall gf, atoms_ok (Ereg regs' (fs_extraT ++ encE_xs regs)) gf ->
     st_ok tfibsegs (Ereg regs' (fs_extraT ++ encE_xs regs)) (fss_retT ENC_RA_MALLOC 48 encE_cs [] gf)
       (restrict (w_H W') (mkst regs' (Z_to_bv 64 ENC_RA_MALLOC) mem' (seg_rom tfibsegs)))) /\
  spZ regs' = spZ regs - 48 /\ getr regs' 8 = getr regs 11 /\ getr regs' 9 = getr regs 10 /\
  getr regs' 18 = w64 SHADOW_OFF /\
  (forall z, acallee_saved z -> z <> 2 -> z <> 8 -> z <> 9 -> z <> 18 ->
     getr regs' (Z_to_bv 5 z) = getr regs (Z_to_bv 5 z)).

(* fuzz_malloc's contract (lib/B/FSH_Fn_alloc.v fuzz_malloc_spec, CTX-free; owner ALLOC; B's FSW_fuzz_malloc.v
   fuzz_malloc_holds discharges it) *)
Hypothesis HMALLOC : fuzz_malloc_spec tfibsegs B.

(* ---- the spine: B 0x84700 -> the call 0x8474c -> fuzz_malloc -> the resumed state at 0x84750 in both arms ---- *)
Lemma encE_spine : forall ly S U W regs mem md ch len live peak cnt fail (Qp : world tfibsegs -> config -> Prop),
  fpreU tfibsegs B STK_preset_base64_encode ly S U W regs mem md ch -> fs_heads B ly S U ->
  getr regs 11 = w64 len -> 0 <= len <= 2 ^ 27 ->
  fs_glob tfibsegs W mem live peak cnt fail ->
  st_nev S + EV_preset_base64_encode <= EV_MAX -> blocks_bytes S + (enc_size len + HEAD) <= LIVE_MAX ->
  live + enc_size len < 2 ^ 64 -> cnt + 1 < 2 ^ 64 ->
  (forall W' ly' S' regs' mem' md', cnt = fail ->
     encE_res ly S U W regs mem md W' ly' S' U regs' mem' md' 0 -> getr regs' 10 = w64 0 ->
     ablocks B ly' S' = ablocks B ly S -> fs_glob tfibsegs W' mem' live peak (cnt + 1) SIZE_MAXZ ->
     SRr tfibsegs W' (mkCfg (mkst regs' (Z_to_bv 64 ENC_RA_MALLOC) mem' (seg_rom tfibsegs)) md') Qp) ->
  (forall q W' ly' S' regs' mem' md', cnt <> fail ->
     encE_res ly S U W regs mem md W' ly' S' (U ++ [(q - HEAD, HEAD)]) regs' mem' md' 1 ->
     getr regs' 10 = w64 q -> 4096 + HEAD <= q ->
     ablocks B ly' S' = ablocks B ly S ++ [(q - HEAD, enc_size len + HEAD)] ->
     fs_heads B ly' S' (U ++ [(q - HEAD, HEAD)]) ->
     fs_rblock tfibsegs B ly' S' W' mem' q (enc_size len) ->
     fs_glob tfibsegs W' mem' (live + enc_size len) (Z.max peak (live + enc_size len)) (cnt + 1) fail ->
     SRr tfibsegs W' (mkCfg (mkst regs' (Z_to_bv 64 ENC_RA_MALLOC) mem' (seg_rom tfibsegs)) md') Qp) ->
  SRr tfibsegs W (cfg_at tfibsegs A_preset_base64_encode regs mem md) Qp.
Proof.
intros ly S U W regs mem md ch len live peak cnt fail Qp HPRE FH H11 HLN HGL HEV HLV HLIVE HCNT KN KS.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof alloc_ceiling_val as (CR & _).
assert (FS : STK_preset_base64_encode = ltac:(let v := eval vm_compute in STK_preset_base64_encode in exact v))
  by reflexivity.
assert (FM : STK_fuzz_malloc = ltac:(let v := eval vm_compute in STK_fuzz_malloc in exact v)) by reflexivity.
pose proof HPRE as (HPREU & HRO).
pose proof (fsw_ARU B STK_preset_base64_encode ly S U W regs mem md ch HPREU) as HARU0.
pose proof HPREU as (HAP & HUOK & HUPO).
pose proof HAP as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof (fsw_sp B STK_preset_base64_encode ly S U W regs mem md ch HPREU) as (Hal16 & Hceil & H47 & HS0).
(* ---- the entry state: the frame, the two shadow-base cells, the .rodata word 0x10320 ---- *)
assert (HROu : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) (unpoison U mem)))
  by exact (encE_aro_unp ly S U W mem md HARU0 HRO).
assert (Vmag : val_mem tfibsegs (mrestrict (w_H W) mem) ENC_MAGIC_A 8 ENC_MAGIC).
{ pose proof IMG as (_ & HIM). destruct (HIM ly S W (unpoison U mem) md HAR HROu) as (HRV & _).
  exact (enc_magic_val ly S U W mem md HARU0 HRV). }
assert (E2 : bv_unsigned (ew (Ereg regs fs_extraT) 2) = spZ regs)
  by (rewrite (ew_Ereg_nat regs fs_extraT 2 2%bv eq_refl); reflexivity).
assert (HS : st_ok tfibsegs (Ereg regs fs_extraT) (fss0T_args A_preset_base64_encode 48 [enc_magic_region] [])
  (restrict (w_H W) (mkst regs (Z_to_bv 64 A_preset_base64_encode) mem (seg_rom tfibsegs)))).
{ apply (fsw_entryT_args B STK_preset_base64_encode 48 ly S U W regs mem md ch A_preset_base64_encode
    [enc_magic_region] [] (proj1 HSS) (proj2 HSS) HPREU).
  - rewrite FS. lia.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    unfold enc_magic_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [unfold ENC_MAGIC_A; lia|]. split; [unfold ENC_MAGIC_A; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val tfibsegs _ _ 0 ENC_MAGIC_A 8 (SLit ENC_MAGIC) ENC_MAGIC);
      [reflexivity | unfold ENC_MAGIC; cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
      | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite Z.add_0_l; exact Vmag].
  - apply pairwise_disjoint_of_extents.
    unfold fsT_regions_args, fsT_regions, fs_got_region, fs_bcell_region, fstk, enc_magic_region, extent_of_region.
    cbn [map app YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2.
    unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address, ENC_MAGIC_A.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat match goal with |- _ /\ _ => split end; try exact I; first [right; lia | left; lia].
  - exact I. }
pose proof (ajournal_init tfibsegs B STK_preset_base64_encode FS_PSTAT_FP ly S W regs (unpoison U mem) md ch HAP)
  as HJ.
unfold cfg_at. change (w64 A_preset_base64_encode) with (Z_to_bv 64 A_preset_base64_encode).
(* ---- run 1: 0x84700 -> fuzz_malloc (the jal 0x8474c) ---- *)
fsw_aj_run_toU fsw_wr_tbl_ok HS HJ HARU0 A_fuzz_malloc.
{ cbv [fss0T_args fsT_regions_args fsT_regions ss_mem app].
  eapply awr_ok_cons_stack with (n := 2%nat);
    [reflexivity | exact E2 | cbv [fstk YP09.r_wlo]; rewrite FS; lia | cbv [fstk YP09.r_whi]; lia |].
  apply awr_ok_cons_ro; [cbv [fs_got_region YP09.r_wlo YP09.r_whi]; lia|].
  apply awr_ok_cons_ro; [cbv [fs_bcell_region YP09.r_wlo YP09.r_whi]; lia|].
  apply awr_ok_cons_ro; [cbv [enc_magic_region YP09.r_wlo YP09.r_whi]; lia|].
  apply awr_ok_nil. }
rename ms into ms1.
lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (mdC := m) in * end.
(* ---- at the call (pc fuzz_malloc, ra 0x84750, a0 = enc_size len, s0 = len, s1 = data, s2 = the shadow base) ---- *)
pose proof (fsw_reg_lit _ _ _ ms1 1%bv ENC_RA_MALLOC HS ltac:(vm_compute; reflexivity)
  ltac:(unfold ENC_RA_MALLOC; lia)) as R1.
pose proof (fsw_reg_off _ _ _ ms1 2%bv 2 (-48) (spZ regs) HS ltac:(vm_compute; reflexivity) E2 ltac:(lia)) as R2.
pose proof (fsw_reg_atom _ regs fs_extraT _ ms1 3%bv 3%bv 3 HS ltac:(vm_compute; reflexivity) eq_refl) as R3.
pose proof (fsw_reg_atom _ regs fs_extraT _ ms1 4%bv 4%bv 4 HS ltac:(vm_compute; reflexivity) eq_refl) as R4.
pose proof (fsw_reg_atom _ regs fs_extraT _ ms1 8%bv 11%bv 11 HS ltac:(vm_compute; reflexivity) eq_refl) as R8.
pose proof (fsw_reg_atom _ regs fs_extraT _ ms1 9%bv 10%bv 10 HS ltac:(vm_compute; reflexivity) eq_refl) as R9.
pose proof (fsw_reg_extra _ regs fs_extraT _ ms1 18%bv 0 HS ltac:(vm_compute; reflexivity)) as R18.
cbn [nth fs_extraT] in R18.
assert (RK1 : forall z, acallee_saved z -> z <> 2 -> z <> 8 -> z <> 9 -> z <> 18 ->
  getr (ms_regs ms1) (Z_to_bv 5 z) = getr regs (Z_to_bv 5 z)).
{ intros z Hz H2 H8 H9 H18. destruct (encE_zs_in z Hz H2 H8 H9 H18) as (Hin & Hz32).
  exact (encE_kept_gen _ regs fs_extraT _ ms1 encE_zs HS ltac:(vm_compute; reflexivity) z Hin Hz32). }
assert (Hspc : spZ (ms_regs ms1) = spZ regs - 48) by (unfold spZ at 1; rewrite R2; lia).
assert (R10c : getr (ms_regs ms1) 10 = w64 (enc_size len)).
{ lazymatch type of HS with st_ok _ _ ?ss _ =>
    rewrite (st_ok_restrict_reg tfibsegs (w_H W) _ ss ms1 10%bv HS);
    assert (Hr10 : sr_get (ss_regs ss) 10%bv = encE_size_sv) by (vm_compute; reflexivity) end.
  rewrite Hr10. apply encE_size_den; [|exact HLN].
  rewrite (ew_Ereg_nat regs fs_extraT 11 11%bv eq_refl). exact H11. }
assert (HFR1 : encE_frame W (ms_mem ms1) regs).
{ apply encE_frame_of_call.
  lazymatch type of HS with st_ok _ _ ?ss _ =>
    pose proof (fsw_region_nth _ ss (restrict (w_H W) ms1) 0 _ HS eq_refl) as HR0 end.
  cbn [ms_mem restrict] in HR0. exact HR0. }
(* the prologue wrote only the frame [sp - 48, sp) *)
assert (MEQ1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 48 <= a < spZ regs) ->
  ms_mem ms1 (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
{ intros a Ha Hna. apply HF. rewrite (wz a Ha). intros (r & Hin & Hr).
  cbv [fss0T_args fsT_regions_args fsT_regions ss_mem app In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
    cbv [fstk fs_got_region fs_bcell_region enc_magic_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    try (rewrite E2 in Hr); lia. }
assert (SB1 : same_below mem (ms_mem ms1) alloc_ceiling)
  by (intros x Hx; apply MEQ1; rewrite FS in Hceil; lia).
pose proof (fs_glob_below W mem (ms_mem ms1) live peak cnt fail SB1 HGL) as HG1.
clear HF HFr HG.
(* ---- the callee's fpreU ---- *)
assert (Hs0c : s0Z (ms_regs ms1) = len) by (unfold s0Z; rewrite R8, H11; unfold w64; apply wz; lia).
assert (HCH : achain ly (aview tfibsegs (w_H W) (unpoison U (ms_mem ms1))) (spZ (ms_regs ms1)) (s0Z (ms_regs ms1)) [])
  by (rewrite Hs0c; apply achain_low; lia).
assert (HRO1 : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) (ms_mem ms1)))
  by exact (arodata_below B W mem (ms_mem ms1) SB1 HRO).
assert (HPREc : fpreU tfibsegs B STK_fuzz_malloc ly S U W (ms_regs ms1) (ms_mem ms1) mdC []).
{ apply (fsw_fpreU_atFP B STK_preset_base64_encode (spZ regs) FS_PSTAT_FP ly S U W (unpoison U mem) md [] ly S W
    (ms_mem ms1) mdC 0 (ms_regs ms1) STK_fuzz_malloc (-48) [] HJ HARU0 HRO1).
  - rewrite Hspc. lia.
  - reflexivity.
  - lia.
  - rewrite FM. lia.
  - rewrite FS, FM. lia.
  - rewrite R1. apply ret_ok_even. rewrite unsigned_lit_small by (unfold ENC_RA_MALLOC; lia). reflexivity.
  - unfold raZ. rewrite R1, unsigned_lit_small by (unfold ENC_RA_MALLOC; lia). unfold ENC_RA_MALLOC. lia.
  - rewrite R3. exact Hgp.
  - rewrite R4. exact Htp.
  - exact HCH. }
assert (HQ3 : 0 <= (len + 2) / 3 <= 2 ^ 27)
  by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (Hn1 : 1 <= enc_size len) by (unfold enc_size; lia).
assert (HQ4 : (len + 2) / 3 < 44739244) by (apply Z.div_lt_upper_bound; lia).
assert (Hn2 : enc_size len + HEAD < MALLOC_MAX) by (unfold enc_size, HEAD, MALLOC_MAX; lia).
assert (HEV1 : st_nev S + 1 <= EV_MAX) by (unfold EV_preset_base64_encode in HEV; exact HEV).
(* ---- the resume after fuzz_malloc, common to both arms ---- *)
assert (AFTER : forall W' ly' S' U' regs' mem' md' kc,
  ajournal tfibsegs B STK_fuzz_malloc (spZ (ms_regs ms1)) FS_PSTAT_FP ly S W (unpoison U (ms_mem ms1)) mdC []
    ly' S' W' (unpoison U' mem') md' kc ->
  upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' -> aregs_preserved (ms_regs ms1) regs' ->
  encE_res ly S U W regs mem md W' ly' S' U' regs' mem' md' (0 + kc)).
{ intros W' ly' S' U' regs' mem' md' kc HJc OK' PO' HP'.
  assert (Hspr : spZ regs' = spZ regs - 48).
  { unfold spZ at 1. rewrite (fsw_pres _ _ 2%bv HP') by encE_cs_side. exact Hspc. }
  assert (G19 : getr regs' 19 = getr regs 19).
  { rewrite (fsw_pres _ _ 19%bv HP') by encE_cs_side.
    exact (RK1 19 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
  assert (G20 : getr regs' 20 = getr regs 20).
  { rewrite (fsw_pres _ _ 20%bv HP') by encE_cs_side.
    exact (RK1 20 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
  pose proof (encE_cs_ok W (ms_mem ms1) regs regs' G19 G20 HFR1) as Hcs.
  assert (HFPS : fsw_fp_sub B ly S ly S [] FS_PSTAT_FP FS_PSTAT_FP).
  { intros a Ha. right; right; left. split; [exact Ha | exact (encE_pstat_img a Ha)]. }
  assert (HPD : pairwise_disjoint (Ereg regs' (fs_extraT ++ encE_xs regs)) (fsT_ret_regions 48 encE_cs [])).
  { apply pairwise_disjoint_of_extents.
    unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, extent_of_region.
    cbn [map app YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite (ew_Ereg_nat regs' _ 2 2%bv eq_refl). change (bv_unsigned (getr regs' 2)) with (spZ regs'). rewrite Hspr.
    unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat match goal with |- _ /\ _ => split end; try exact I; first [right; lia | left; lia]. }
  assert (ST : forall gf, atoms_ok (Ereg regs' (fs_extraT ++ encE_xs regs)) gf ->
    ajournal tfibsegs B STK_preset_base64_encode (spZ regs) FS_PSTAT_FP ly S W (unpoison U mem) md []
      ly' S' W' (unpoison U' mem') md' (0 + kc) /\
    ARU tfibsegs B ly' S' U' W' mem' md' /\
    st_ok tfibsegs (Ereg regs' (fs_extraT ++ encE_xs regs)) (fss_retT ENC_RA_MALLOC 48 encE_cs [] gf)
      (restrict (w_H W') (mkst regs' (Z_to_bv 64 ENC_RA_MALLOC) mem' (seg_rom tfibsegs)))).
  { intros gf Hgf.
    exact (fsw_after_callFPU_args B STK_preset_base64_encode (spZ regs) FS_PSTAT_FP [] ly S U W mem md W ly S U
      (ms_mem ms1) mdC 0 STK_fuzz_malloc FS_PSTAT_FP 48 (ms_regs ms1) ly' S' U' W' regs' mem' md' kc
      (encE_xs regs) encE_cs [] gf ENC_RA_MALLOC (proj1 HSS) (proj2 HSS) HJ HARU0 HJc HFPS OK' PO' HP' Hspc
      ltac:(lia) ltac:(rewrite FM; lia) ltac:(rewrite FS, FM; lia) eq_refl ltac:(vm_compute; reflexivity)
      ltac:(repeat constructor; cbn; lia) Hcs (Forall_nil _) HPD Hgf). }
  destruct (ST [] I) as (HJ' & HARU' & _).
  split; [exact HJ'|]. split; [exact HARU'|].
  split; [intros gf Hgf; exact (proj2 (proj2 (ST gf Hgf)))|].
  split; [exact Hspr|].
  split; [rewrite (fsw_pres _ _ 8%bv HP') by encE_cs_side; exact R8|].
  split; [rewrite (fsw_pres _ _ 9%bv HP') by encE_cs_side; exact R9|].
  split; [rewrite (fsw_pres _ _ 18%bv HP') by encE_cs_side; exact R18|].
  intros z Hz H2 H8 H9 H18. rewrite (HP' z Hz). exact (RK1 z Hz H2 H8 H9 H18). }
(* ---- the call ---- *)
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ _ ms1 HS eq_refl). cbn [ss_pc].
eapply SRr_bind; [exact (HMALLOC ly S U W (ms_regs ms1) (ms_mem ms1) mdC [] (enc_size len) live peak cnt fail
  HPREc FH R10c Hn1 Hn2 HG1 (fun _ => HLIVE) HCNT HEV1 (fun _ => HLV))|].
intros W' c' _ [(Hcf & HQ1) | (Hcf & res & HQ2)].
- destruct HQ1 as (ly' & S' & regs' & mem' & md' & -> & HJc & OK' & PO' & HP' & H10' & Hbl' & HH' & HG').
  rewrite R1.
  exact (KN W' ly' S' regs' mem' md' Hcf (AFTER W' ly' S' U regs' mem' md' 0 HJc OK' PO' HP') H10' Hbl' HG').
- destruct HQ2 as (ly' & S' & regs' & mem' & md' & -> & HJc & OK' & PO' & HP' & H10' & Hres4 & Hbl' & HH' & Hrb
    & Hra' & HG').
  rewrite R1.
  exact (KS res W' ly' S' regs' mem' md' Hcf (AFTER W' ly' S' _ regs' mem' md' 1 HJc OK' PO' HP') H10' Hres4 Hbl' HH'
    (Hrb ltac:(lia)) HG').
Qed.

(* ---- the refused arm: a0 = 0, `beqz a0` 0x84750 taken, the epilogue 0x84b38 .. the ret 0x84b54 ---- *)
Lemma encE_null : forall ly S U W regs mem md ch live peak cnt W' ly' S' regs' mem' md',
  fpreU tfibsegs B STK_preset_base64_encode ly S U W regs mem md ch -> cnt + 1 < 2 ^ 64 ->
  encE_res ly S U W regs mem md W' ly' S' U regs' mem' md' 0 -> getr regs' 10 = w64 0 ->
  ablocks B ly' S' = ablocks B ly S -> fs_glob tfibsegs W' mem' live peak (cnt + 1) SIZE_MAXZ ->
  SRr tfibsegs W' (mkCfg (mkst regs' (Z_to_bv 64 ENC_RA_MALLOC) mem' (seg_rom tfibsegs)) md')
    (fpostU tfibsegs B STK_preset_base64_encode (spZ regs) FS_PSTAT_FP regs ly S U W mem md 0 U
       (fun ly2 S2 W2 regs2 mem2 md2 =>
          getr regs2 10 = w64 0 /\ ablocks B ly2 S2 = ablocks B ly S /\
          fs_glob tfibsegs W2 mem2 live peak ((cnt + 1) mod 2 ^ 64) SIZE_MAXZ)).
Proof.
intros ly S U W regs mem md ch live peak cnt W' ly' S' regs' mem' md' HPRE HCNT HRES HA0 HBL HG'.
pose proof alloc_ceiling_val as (CR & _).
assert (FS : STK_preset_base64_encode = ltac:(let v := eval vm_compute in STK_preset_base64_encode in exact v))
  by reflexivity.
pose proof HPRE as (HPREU & _).
pose proof HPREU as (HAP & _ & _).
pose proof HAP as (HAR & Hra & _).
pose proof (fsw_sp B STK_preset_base64_encode ly S U W regs mem md ch HPREU) as (Hal16 & Hceil & H47 & HS0).
destruct HRES as (HJ & HARU & HST & Gsp & G8 & G9 & G18 & GK).
assert (E2 : bv_unsigned (ew (Ereg regs' (fs_extraT ++ encE_xs regs)) 2) = spZ regs - 48)
  by (rewrite (ew_Ereg_nat regs' _ 2 2%bv eq_refl); exact Gsp).
assert (Hcnt0 : 0 <= cnt + 1) by (destruct HG' as (_ & _ & _ & _ & _ & _ & Hc & _); lia).
assert (HS : st_ok tfibsegs (Ereg regs' (fs_extraT ++ encE_xs regs))
  (add_cond (fss_retT ENC_RA_MALLOC 48 encE_cs [] []) (mkAC BC_EQ (SOff 10 0) (SLit 0)))
  (restrict (w_H W') (mkst regs' (Z_to_bv 64 ENC_RA_MALLOC) mem' (seg_rom tfibsegs)))).
{ apply YP06.st_ok_add_cond; [exact (HST [] I)|].
  rewrite fsw_SOff0, (ew_Ereg_nat regs' _ 10 10%bv eq_refl), HA0. vm_compute. reflexivity. }
fsw_aj_runU fsw_wr_tbl_ok HS HJ HARU.
- (* the run reads the frame back and writes nothing *)
  unfold add_cond, fss_retT, fsT_ret_regions. cbn [ss_mem app].
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -48);
    [reflexivity | rewrite E2; lia | cbv [fstk_ret YP09.r_wlo]; rewrite FS; lia | cbv [fstk_ret YP09.r_whi]; lia |].
  apply awr_ok_cons_ro; [cbv [fs_got_region YP09.r_wlo YP09.r_whi]; lia|].
  apply awr_ok_cons_ro; [cbv [fs_bcell_region YP09.r_wlo YP09.r_whi]; lia|].
  apply awr_ok_nil.
- assert (MEQ : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 48 <= a < spZ regs) ->
    ms_mem ms (Z_to_bv 64 a) = mem' (Z_to_bv 64 a)).
  { intros a Ha Hna. apply HF. rewrite (wz a Ha). intros (r & Hin & Hr).
    unfold add_cond, fss_retT, fsT_ret_regions in Hin. cbn [ss_mem app In] in Hin.
    destruct Hin as [<-|[<-|[<-|[]]]];
      cbv [fstk_ret fs_got_region fs_bcell_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
      try (rewrite E2 in Hr); lia. }
  assert (SB : same_below mem' (ms_mem ms) alloc_ceiling)
    by (intros x Hx; apply MEQ; rewrite FS in Hceil; lia).
  assert (R1 : getr (ms_regs ms) 1%bv = getr regs 1%bv).
  { lazymatch type of HS with
    | st_ok _ _ ?ssf _ =>
      exact (fsw_reg_extra (w_H W') regs' (fs_extraT ++ encE_xs regs) ssf ms 1%bv 1 HS ltac:(vm_compute; reflexivity))
    end. }
  eapply (fsw_retU B fsw_wr_tbl fsw_wr_tbl_ok).
  + exact HS.
  + vm_compute; reflexivity.
  + vm_compute; reflexivity.
  + rewrite R1. exact Hra.
  + exact HJ.
  + exact HARU.
  + (* the callee-saved registers: sp = atom 2 + 48, s0 / s1 / s2 the reloaded extra atoms, the others kept *)
    lazymatch type of HS with
    | st_ok _ _ ?ssf _ =>
      apply (fsw_preserved (w_H W') (Ereg regs' (fs_extraT ++ encE_xs regs)) ssf ms regs
        (fun r : bv 5 => sr_get (ss_regs ssf) r) HS);
      [vm_compute; reflexivity|];
      let r := fresh "r" in let Hr := fresh "Hr" in
      intros r Hr; cbv [CALLEE_SAVED In] in Hr;
      repeat (destruct Hr as [<-|Hr]); [..|destruct Hr]
    end;
    cbv beta;
    lazymatch goal with
    | |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e'
    end;
    first
    [ apply fsw_sp_back; rewrite E2; lia
    | rewrite fsw_SOff0;
      first
      [ lazymatch goal with |- ew _ ?n = getr _ ?q =>
          rewrite (ew_Ereg_nat regs' _ n q eq_refl);
          let z := eval vm_compute in (bv_unsigned q) in
          exact (GK z ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) end
      | lazymatch goal with |- ew _ ?n = _ =>
          let j := eval compute in (n - 32)%nat in change n with (32 + j)%nat end;
        rewrite ew_Ereg_extra; reflexivity ] ].
  + intros mat2. cbv beta.
    split.
    { rewrite (fsw_reg_atom _ regs' _ _ ms 10%bv 10%bv 10 HS ltac:(vm_compute; reflexivity) eq_refl). exact HA0. }
    split; [exact HBL|].
    rewrite Z.mod_small by lia. exact (fs_glob_below W' mem' (ms_mem ms) _ _ _ _ SB HG').
Qed.

(* ---- from the call's post to Section R's hypotheses and encR_inv, at the hand-over memory m2 ---- *)
Lemma encE_at : forall ly S U W regs mem md ch data len (bs : list Z) live peak cnt fail kd q W' ly' S' mem' m2 md2,
  fpreU tfibsegs B STK_preset_base64_encode ly S U W regs mem md ch ->
  WriterSpec.bytes_ok bs -> Z.of_nat (length bs) = len -> 0 <= len <= 2 ^ 27 ->
  zbytes_at tfibsegs W mem data bs -> 4096 <= data -> data + len <= alloc_ceiling ->
  (0 < len -> In (data - HEAD, kd + HEAD) (ablocks B ly S) /\ len <= kd /\ 0 < kd) ->
  ajournal tfibsegs B STK_preset_base64_encode (spZ regs) FS_PSTAT_FP ly S W (unpoison U mem) md []
    ly' S' W' (unpoison (U ++ [(q - HEAD, HEAD)]) m2) md2 1 ->
  ARU tfibsegs B ly' S' (U ++ [(q - HEAD, HEAD)]) W' m2 md2 ->
  fs_heads B ly' S' (U ++ [(q - HEAD, HEAD)]) -> 4096 + HEAD <= q ->
  ablocks B ly' S' = ablocks B ly S ++ [(q - HEAD, enc_size len + HEAD)] ->
  fs_rblock tfibsegs B ly' S' W' mem' q (enc_size len) ->
  fs_glob tfibsegs W' mem' (live + enc_size len) (Z.max peak (live + enc_size len)) (cnt + 1) fail ->
  same_below mem' m2 alloc_ceiling -> encE_frame W' m2 regs ->
  encE_Rhyps ly S U W mem regs ly' S' W' m2 md2 data len q live peak cnt fail kd bs /\
  encR_inv B ly S U W mem md regs ly' S' W' m2 len q m2 md2.
Proof.
intros ly S U W regs mem md ch data len bs live peak cnt fail kd q W' ly' S' mem' m2 md2 HPRE HBS HBSL HLN HZB HDLO
  HDHI HDB HJ2 HARU2 HH' Hq16 Hbl' HRB' HG' SB HFR.
pose proof HPRE as (HPREU & HRO).
pose proof (fsw_ARU B STK_preset_base64_encode ly S U W regs mem md ch HPREU) as HARU0.
pose proof HPREU as (HAP & _ & _).
pose proof HAP as (HAR & Hra & _).
pose proof (fsw_sp B STK_preset_base64_encode ly S U W regs mem md ch HPREU) as (Hal16 & Hceil & H47 & HS0).
pose proof alloc_ceiling_val as (CR & _).
pose proof HARU2 as (_ & OK2 & PO2).
assert (HQB : In (q - HEAD, enc_size len + HEAD) (ablocks B ly' S'))
  by (rewrite Hbl'; apply in_or_app; right; left; reflexivity).
pose proof (encR_size_pos len bs HLN HBSL) as HM.
pose proof (encR_out_facts B U ly' S' W' m2 md2 len q bs HLN HBSL HARU2 HQB) as (_ & HQceil & _).
assert (HRO2 : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W') m2))
  by exact (FSW_rd.arodata_kept B STK_preset_base64_encode (spZ regs) FS_PSTAT_FP ly S U W mem md ly' S' _ W' m2 md2
              1 HJ2 HARU0 OK2 PO2 encE_pstat_closed encE_ro_not_pstat HRO).
destruct (enc_table ly' S' _ W' m2 md2 HARU2 HH' (encE_aro_unp ly' S' _ W' m2 md2 HARU2 HRO2)) as (HTAB & HRAT).
pose proof (encE_keep ly S U W mem md ly' S' _ W' m2 md2 1 (spZ regs) data len kd _ HJ2 HARU0 HARU2 Hbl' HDB)
  as HKEEP.
assert (HDAT : garr8 tfibsegs (mrestrict (w_H W') m2) data bs).
{ unfold zbytes_at in HZB. apply (garr8_frame tfibsegs (mrestrict (w_H W) mem) _ data bs HZB).
  intros a Ha. rewrite HBSL in Ha. replace a with (data + (a - data)) by lia. apply HKEEP. lia. }
assert (HRB2 : fs_rblock tfibsegs B ly' S' W' m2 q (enc_size len)).
{ destruct HRB' as (Hin & H16 & Hpos & Hv). split; [exact Hin|]. split; [exact H16|]. split; [exact Hpos|].
  apply (val_mem_below (w_H W') mem' m2 alloc_ceiling (q - HEAD) 8 (enc_size len) SB);
    [unfold HEAD in *; lia | cbn [Z.of_nat]; unfold HEAD in *; lia | exact Hv]. }
assert (HG2 : fs_glob tfibsegs W' m2 (live + enc_size len) (Z.max peak (live + enc_size len))
  ((cnt + 1) mod 2 ^ 64) fail).
{ rewrite Z.mod_small by (destruct HG' as (_ & _ & _ & _ & _ & _ & Hc & _); lia).
  exact (fs_glob_below W' mem' m2 _ _ _ _ SB HG'). }
split.
- unfold encE_Rhyps.
  exact (conj HLN (conj HBS (conj HBSL (conj HDLO (conj HDHI (conj HARU2 (conj HH' (conj HQB (conj Hbl'
    (conj Hq16 (conj HDB (conj HRB2 (conj HG2 (conj HTAB (conj HRAT (conj HDAT (conj HKEEP (conj HFR
    (conj (conj Hal16 (conj Hceil H47)) Hra))))))))))))))))))).
- unfold encR_inv, encR_J, encR_agree.
  split; [exact HJ2|]. split; [exact HARU2|]. intros x _. reflexivity.
Qed.

(* ---- the granted arm: a0 = q, `beqz a0` 0x84750 not taken, the len < 3 dispatch, and the hand-over ---- *)
Lemma encE_succ : forall ly S U W regs mem md ch data len (bs : list Z) live peak cnt fail q W' ly' S' regs' mem' md',
  fpreU tfibsegs B STK_preset_base64_encode ly S U W regs mem md ch ->
  getr regs 10 = w64 data -> getr regs 11 = w64 len ->
  WriterSpec.bytes_ok bs -> Z.of_nat (length bs) = len -> 0 <= len <= 2 ^ 27 ->
  zbytes_at tfibsegs W mem data bs -> 4096 <= data /\ data + len <= alloc_ceiling ->
  (0 < len -> exists kd, fs_rblock tfibsegs B ly S W mem data kd /\ len <= kd) ->
  encE_KLOOP ly S U W regs mem md data len bs live peak cnt fail ->
  encE_KTAIL ly S U W regs mem md data len bs live peak cnt fail ->
  cnt <> fail ->
  encE_res ly S U W regs mem md W' ly' S' (U ++ [(q - HEAD, HEAD)]) regs' mem' md' 1 ->
  getr regs' 10 = w64 q -> 4096 + HEAD <= q ->
  ablocks B ly' S' = ablocks B ly S ++ [(q - HEAD, enc_size len + HEAD)] ->
  fs_heads B ly' S' (U ++ [(q - HEAD, HEAD)]) ->
  fs_rblock tfibsegs B ly' S' W' mem' q (enc_size len) ->
  fs_glob tfibsegs W' mem' (live + enc_size len) (Z.max peak (live + enc_size len)) (cnt + 1) fail ->
  SRr tfibsegs W' (mkCfg (mkst regs' (Z_to_bv 64 ENC_RA_MALLOC) mem' (seg_rom tfibsegs)) md')
    (encE_post ly S U W regs mem md data len bs live peak cnt fail).
Proof.
intros ly S U W regs mem md ch data len bs live peak cnt fail q W' ly' S' regs' mem' md' HPRE H10 H11 HBS HBSL HLN
  HZB (HDLO & HDHI) HRB KLOOP KTAIL Hcf HRES H10' Hq16 Hbl' HH' Hrb HG'.
pose proof alloc_ceiling_val as (CR & _).
assert (FS : STK_preset_base64_encode = ltac:(let v := eval vm_compute in STK_preset_base64_encode in exact v))
  by reflexivity.
pose proof HPRE as (HPREU & _).
pose proof (fsw_sp B STK_preset_base64_encode ly S U W regs mem md ch HPREU) as (Hal16 & Hceil & H47 & HS0).
destruct HRES as (HJ & HARU & HST & Gsp & G8 & G9 & G18 & GK).
(* the input block (when len > 0), as Section R's HDB *)
assert (HKD : exists kd, 0 < len -> In (data - HEAD, kd + HEAD) (ablocks B ly S) /\ len <= kd /\ 0 < kd).
{ destruct (Z_lt_le_dec 0 len) as [Hp|Hp].
  - destruct (HRB Hp) as (kd & (Hin & _ & Hpos & _) & Hkd). exists kd. intros _. split; [exact Hin | lia].
  - exists 0. intros Hc. lia. }
destruct HKD as (kd & HDB).
assert (HQB : In (q - HEAD, enc_size len + HEAD) (ablocks B ly' S'))
  by (rewrite Hbl'; apply in_or_app; right; left; reflexivity).
pose proof (encR_size_pos len bs HLN HBSL) as HM.
pose proof (encR_out_facts B U ly' S' W' mem' md' len q bs HLN HBSL HARU HQB) as (_ & HQceil & _).
assert (E2 : bv_unsigned (ew (Ereg regs' (fs_extraT ++ encE_xs regs)) 2) = spZ regs - 48)
  by (rewrite (ew_Ereg_nat regs' _ 2 2%bv eq_refl); exact Gsp).
assert (E8 : ew (Ereg regs' (fs_extraT ++ encE_xs regs)) 8 = w64 len)
  by (rewrite (ew_Ereg_nat regs' _ 8 8%bv eq_refl), G8; exact H11).
assert (E9 : ew (Ereg regs' (fs_extraT ++ encE_xs regs)) 9 = w64 data)
  by (rewrite (ew_Ereg_nat regs' _ 9 9%bv eq_refl), G9; exact H10).
assert (E10 : ew (Ereg regs' (fs_extraT ++ encE_xs regs)) 10 = w64 q)
  by (rewrite (ew_Ereg_nat regs' _ 10 10%bv eq_refl); exact H10').
assert (U9 : bv_unsigned (ew (Ereg regs' (fs_extraT ++ encE_xs regs)) 9) = data)
  by (rewrite E9; unfold w64; apply wz; lia).
assert (GF : forall lo hi, lo <= len <= hi -> atoms_ok (Ereg regs' (fs_extraT ++ encE_xs regs)) (encE_gf lo hi)).
{ intros lo hi Hlh. unfold encE_gf. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E8, E9, E10. unfold w64. rewrite !wz by (unfold HEAD in *; lia). rewrite Z.pow_0_r, !Z.mod_1_r.
  unfold PTOP. repeat split; unfold HEAD in *; lia. }
assert (G19 : getr regs' 19 = getr regs 19)
  by exact (GK 19 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
assert (G20 : getr regs' 20 = getr regs 20)
  by exact (GK 20 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
(* the success arm of encode_spec's post, from the hand-over continuations' fpostU *)
assert (WRAP : forall c, SRr tfibsegs W' c
    (fpostU tfibsegs B STK_preset_base64_encode (spZ regs) FS_PSTAT_FP regs ly S U W mem md
       EV_preset_base64_encode (U ++ [(q - HEAD, HEAD)]) (encR_Q B ly S W mem data len q live peak cnt fail bs)) ->
  SRr tfibsegs W' c (encE_post ly S U W regs mem md data len bs live peak cnt fail)).
{ intros c Hc. eapply SRr_mono; [exact Hc|]. intros W2 c2 _ HP. right. exists q.
  split; [exact Hcf|]. split; [unfold HEAD in *; lia|]. exact HP. }
assert (HPRE0 : forall (m : word -> option byte),
  garr8 tfibsegs m q (WriterSpec.b64_enc (firstn (Z.to_nat (3 * 0)) bs)))
  by (intros m; exact (garr8_nil tfibsegs m q)).
(* the memory after a run from the resumed state, which writes nothing *)
assert (MEQ_of : forall msx gf, frame_of (Ereg regs' (fs_extraT ++ encE_xs regs))
    (ss_mem (fss_retT ENC_RA_MALLOC 48 encE_cs [] gf)) mem' (ms_mem msx) ->
  same_below mem' (ms_mem msx) alloc_ceiling).
{ intros msx gf HF x Hx. apply HF. rewrite (wz x ltac:(lia)). intros (r & Hin & Hr).
  cbv [fss_retT fsT_ret_regions ss_mem app In] in Hin.
  destruct Hin as [<-|[<-|[<-|[]]]];
    cbv [fstk_ret fs_got_region fs_bcell_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    try (rewrite E2 in Hr); rewrite FS in Hceil; lia. }
destruct (Z_lt_le_dec len 3) as [Hl3 | Hl3].
- destruct (Z.eq_dec len 0) as [Hl0 | Hl0].
  + (* ---- len = 0: to the NUL 0x84b24 ---- *)
    pose proof (HST _ (GF 0 0 ltac:(lia))) as HS.
    fsw_aj_run_toU fsw_wr_tbl_ok HS HJ HARU ENC_NUL.
    { unfold fss_retT, fsT_ret_regions. cbn [ss_mem app].
      eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -48);
        [reflexivity | rewrite E2; lia | cbv [fstk_ret YP09.r_wlo]; rewrite FS; lia | cbv [fstk_ret YP09.r_whi]; lia |].
      apply awr_ok_cons_ro; [cbv [fs_got_region YP09.r_wlo YP09.r_whi]; lia|].
      apply awr_ok_cons_ro; [cbv [fs_bcell_region YP09.r_wlo YP09.r_whi]; lia|].
      apply awr_ok_nil. }
    pose proof (MEQ_of ms _ HF) as SB.
    assert (HFR : encE_frame W' (ms_mem ms) regs).
    { lazymatch type of HS with st_ok _ _ ?ss _ =>
        pose proof (fsw_region_nth _ ss (restrict (w_H W') ms) 0 _ HS eq_refl) as HR0 end.
      cbn [ms_mem restrict] in HR0. exact (encE_frame_of_ret W' (ms_mem ms) regs regs' G19 G20 E2 HR0). }
    destruct (encE_at ly S U W regs mem md ch data len bs live peak cnt fail kd q W' ly' S' mem' (ms_mem ms) _ HPRE
      HBS HBSL HLN HZB HDLO HDHI HDB HJ HARU HH' Hq16 Hbl' Hrb HG' SB HFR) as (HRH & HINV).
    destruct HRH as (RLN & _ & RBSL & RDLO & RDHI & RARU & RHH & RQB & RAB & RQ16 & RDB & RRB & RGL & _ & _ & _ &
      RKEEP & RFR & RSP & RRA).
    pose proof (st_ok_restrict_mkst tfibsegs (w_H W') _ _ ms HS eq_refl) as Hms. cbn [ss_pc] in Hms.
    assert (Hbs : bs = []) by (destruct bs as [|b bs0]; [reflexivity | cbn [length] in HBSL; lia]).
    apply WRAP.
    refine (encR_nul B ly S U W mem md regs ly' S' W' (ms_mem ms) _ data len q live peak cnt fail kd bs
      RLN RBSL RDLO RDHI RARU RHH RQB RAB RQ16 RDB RRB RGL RKEEP RFR RSP RRA ms _ HINV _ Hms _ _ _ _ _).
    * rewrite Hbs. exact (garr8_nil tfibsegs _ q).
    * rewrite (fsw_reg_atom _ regs' _ _ ms 10%bv 10%bv 10 HS ltac:(vm_compute; reflexivity) eq_refl). exact H10'.
    * rewrite (fsw_reg_atom _ regs' _ _ ms 11%bv 10%bv 10 HS ltac:(vm_compute; reflexivity) eq_refl), H10'.
      rewrite Hl0. change ((0 + 2) / 3) with 0. rewrite Z.mul_0_r, Z.add_0_r. reflexivity.
    * rewrite (fsw_reg_atom _ regs' _ _ ms 18%bv 18%bv 18 HS ltac:(vm_compute; reflexivity) eq_refl). exact G18.
    * unfold spZ at 1.
      rewrite (fsw_reg_atom _ regs' _ _ ms 2%bv 2%bv 2 HS ltac:(vm_compute; reflexivity) eq_refl). exact Gsp.
    * intros z Hz H2 H8 H9 H18 _ _. destruct (encE_zs_in z Hz H2 H8 H9 H18) as (Hin & Hz32).
      rewrite (encE_kept_gen _ regs' _ _ ms encE_zs HS ltac:(vm_compute; reflexivity) z Hin Hz32).
      exact (GK z Hz H2 H8 H9 H18).
  + (* ---- len in {1, 2}: to the tail entry 0x849bc ---- *)
    pose proof (HST _ (GF 1 2 ltac:(lia))) as HS.
    fsw_aj_run_toU fsw_wr_tbl_ok HS HJ HARU ENC_TAIL.
    { unfold fss_retT, fsT_ret_regions. cbn [ss_mem app].
      eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -48);
        [reflexivity | rewrite E2; lia | cbv [fstk_ret YP09.r_wlo]; rewrite FS; lia | cbv [fstk_ret YP09.r_whi]; lia |].
      apply awr_ok_cons_ro; [cbv [fs_got_region YP09.r_wlo YP09.r_whi]; lia|].
      apply awr_ok_cons_ro; [cbv [fs_bcell_region YP09.r_wlo YP09.r_whi]; lia|].
      apply awr_ok_nil. }
    pose proof (MEQ_of ms _ HF) as SB.
    assert (HFR : encE_frame W' (ms_mem ms) regs).
    { lazymatch type of HS with st_ok _ _ ?ss _ =>
        pose proof (fsw_region_nth _ ss (restrict (w_H W') ms) 0 _ HS eq_refl) as HR0 end.
      cbn [ms_mem restrict] in HR0. exact (encE_frame_of_ret W' (ms_mem ms) regs regs' G19 G20 E2 HR0). }
    destruct (encE_at ly S U W regs mem md ch data len bs live peak cnt fail kd q W' ly' S' mem' (ms_mem ms) _ HPRE
      HBS HBSL HLN HZB HDLO HDHI HDB HJ HARU HH' Hq16 Hbl' Hrb HG' SB HFR) as (HRH & HINV).
    pose proof (st_ok_restrict_mkst tfibsegs (w_H W') _ _ ms HS eq_refl) as Hms. cbn [ss_pc] in Hms.
    assert (HER : encR_exit_regs regs data len q ms 0).
    { unfold encR_exit_regs.
      split; [rewrite (fsw_reg_atom _ regs' _ _ ms 8%bv 8%bv 8 HS ltac:(vm_compute; reflexivity) eq_refl), G8;
              exact H11|].
      split; [rewrite (fsw_reg_atom _ regs' _ _ ms 9%bv 9%bv 9 HS ltac:(vm_compute; reflexivity) eq_refl), G9;
              exact H10|].
      split; [rewrite (fsw_reg_atom _ regs' _ _ ms 10%bv 10%bv 10 HS ltac:(vm_compute; reflexivity) eq_refl);
              exact H10'|].
      split; [rewrite (fsw_reg_atom _ regs' _ _ ms 11%bv 10%bv 10 HS ltac:(vm_compute; reflexivity) eq_refl), H10';
              rewrite Z.mul_0_r, Z.add_0_r; reflexivity|].
      split; [exact (fsw_reg_lit _ _ _ ms 13%bv 0 HS ltac:(vm_compute; reflexivity) ltac:(lia))|].
      split; [exact (fsw_reg_lit _ _ _ ms 14%bv 135264 HS ltac:(vm_compute; reflexivity) ltac:(lia))|].
      split; [rewrite (fsw_reg_atom _ regs' _ _ ms 18%bv 18%bv 18 HS ltac:(vm_compute; reflexivity) eq_refl);
              exact G18|].
      split; [unfold spZ at 1;
              rewrite (fsw_reg_atom _ regs' _ _ ms 2%bv 2%bv 2 HS ltac:(vm_compute; reflexivity) eq_refl); exact Gsp|].
      intros z Hz H2 H8 H9 H18 _ _. destruct (encE_zs_in z Hz H2 H8 H9 H18) as (Hin & Hz32).
      rewrite (encE_kept_gen _ regs' _ _ ms encE_zs HS ltac:(vm_compute; reflexivity) z Hin Hz32).
      exact (GK z Hz H2 H8 H9 H18). }
    apply WRAP.
    exact (KTAIL ly' S' W' q kd ms _ HRH (Z.le_refl 0) ltac:(lia) ltac:(lia) HINV HER Hms (HPRE0 _)).
- (* ---- 3 <= len: 0x84764 .. 0x84784, to the loop head 0x84788 ---- *)
  pose proof (HST _ (GF 3 (2 ^ 27) ltac:(lia))) as HS.
  fsw_aj_run_toU fsw_wr_tbl_ok HS HJ HARU ENC_HEAD.
  { unfold fss_retT, fsT_ret_regions. cbn [ss_mem app].
    eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -48);
      [reflexivity | rewrite E2; lia | cbv [fstk_ret YP09.r_wlo]; rewrite FS; lia | cbv [fstk_ret YP09.r_whi]; lia |].
    apply awr_ok_cons_ro; [cbv [fs_got_region YP09.r_wlo YP09.r_whi]; lia|].
    apply awr_ok_cons_ro; [cbv [fs_bcell_region YP09.r_wlo YP09.r_whi]; lia|].
    apply awr_ok_nil. }
  pose proof (MEQ_of ms _ HF) as SB.
  assert (HFR : encE_frame W' (ms_mem ms) regs).
  { lazymatch type of HS with st_ok _ _ ?ss _ =>
      pose proof (fsw_region_nth _ ss (restrict (w_H W') ms) 0 _ HS eq_refl) as HR0 end.
    cbn [ms_mem restrict] in HR0. exact (encE_frame_of_ret W' (ms_mem ms) regs regs' G19 G20 E2 HR0). }
  destruct (encE_at ly S U W regs mem md ch data len bs live peak cnt fail kd q W' ly' S' mem' (ms_mem ms) _ HPRE
    HBS HBSL HLN HZB HDLO HDHI HDB HJ HARU HH' Hq16 Hbl' Hrb HG' SB HFR) as (HRH & HINV).
  assert (X16 : getr (ms_regs ms) 16 = w64 (18446744073709551615 - data)).
  { lazymatch type of HS with st_ok _ _ ?ss _ =>
      rewrite (st_ok_restrict_reg tfibsegs (w_H W') _ ss ms 16%bv HS);
      assert (Hr : sr_get (ss_regs ss) 16%bv = SAlu ALU_XOR (SOff 9 0) (SLit (-1))) by (vm_compute; reflexivity) end.
    rewrite Hr, denot_lit_U, U_SAlu. cbn [zalu_raw].
    rewrite (U_atom _ 9 data E9) by lia. rewrite U_SLit. change (zcanon (-1)) with 18446744073709551615.
    rewrite (FSW_preset_base64_encode_ub.enc_ub_not data) by lia.
    unfold w64. f_equal. apply zcanon_id. unfold M64. lia. }
  assert (HLR : encR_loop_regs regs data len q ms 0).
  { unfold encR_loop_regs.
    split; [exact (fsw_reg_lit _ _ _ ms 5%bv 1 HS ltac:(vm_compute; reflexivity) ltac:(lia))|].
    split; [exact (fsw_reg_lit _ _ _ ms 6%bv 18446744073709416351 HS ltac:(vm_compute; reflexivity) ltac:(lia))|].
    split; [exact (fsw_reg_lit _ _ _ ms 7%bv 18446744073709551615 HS ltac:(vm_compute; reflexivity) ltac:(lia))|].
    split; [rewrite (fsw_reg_atom _ regs' _ _ ms 8%bv 8%bv 8 HS ltac:(vm_compute; reflexivity) eq_refl), G8;
            exact H11|].
    split; [rewrite (fsw_reg_atom _ regs' _ _ ms 9%bv 9%bv 9 HS ltac:(vm_compute; reflexivity) eq_refl), G9;
            exact H10|].
    split; [rewrite (fsw_reg_atom _ regs' _ _ ms 10%bv 10%bv 10 HS ltac:(vm_compute; reflexivity) eq_refl);
            exact H10'|].
    split; [rewrite (fsw_reg_atom _ regs' _ _ ms 11%bv 10%bv 10 HS ltac:(vm_compute; reflexivity) eq_refl), H10';
            rewrite Z.mul_0_r, Z.add_0_r; reflexivity|].
    split; [replace (data + 3 * 0 + 2) with (data + 2) by lia;
            exact (enc_reg_val _ _ _ ms 12%bv 9 2 data HS ltac:(vm_compute; reflexivity) U9 ltac:(lia))|].
    split; [exact (fsw_reg_lit _ _ _ ms 14%bv 135264 HS ltac:(vm_compute; reflexivity) ltac:(lia))|].
    split; [exact (fsw_reg_lit _ _ _ ms 15%bv 2 HS ltac:(vm_compute; reflexivity) ltac:(lia))|].
    split; [exact X16|].
    split; [exact (enc_reg_val _ _ _ ms 17%bv 9 1 data HS ltac:(vm_compute; reflexivity) U9 ltac:(lia))|].
    split; [rewrite (fsw_reg_atom _ regs' _ _ ms 18%bv 18%bv 18 HS ltac:(vm_compute; reflexivity) eq_refl);
            exact G18|].
    split; [rewrite (fsw_reg_atom _ regs' _ _ ms 31%bv 10%bv 10 HS ltac:(vm_compute; reflexivity) eq_refl), H10';
            rewrite Z.mul_0_r, Z.add_0_r; reflexivity|].
    split; [unfold spZ at 1;
            rewrite (fsw_reg_atom _ regs' _ _ ms 2%bv 2%bv 2 HS ltac:(vm_compute; reflexivity) eq_refl); exact Gsp|].
    intros z Hz H2 H8 H9 H18 _ _. destruct (encE_zs_in z Hz H2 H8 H9 H18) as (Hin & Hz32).
    rewrite (encE_kept_gen _ regs' _ _ ms encE_zs HS ltac:(vm_compute; reflexivity) z Hin Hz32).
    exact (GK z Hz H2 H8 H9 H18). }
  apply WRAP.
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W') _ _ ms HS eq_refl). cbn [ss_pc].
  exact (KLOOP ly' S' W' q kd ms _ HRH (Z.le_refl 0) ltac:(lia) HINV HLR (HPRE0 _)).
Qed.

(* ---- the entry, from encode_spec's premises and the two continuations ---- *)
Lemma encE_entry : forall ly S U W regs mem md ch data len (bs : list Z) live peak cnt fail,
  fpreU tfibsegs B STK_preset_base64_encode ly S U W regs mem md ch -> fs_heads B ly S U ->
  Z.of_nat (length (frames S)) <= FRL_CRT_CALLEE ->
  getr regs 10 = w64 data -> getr regs 11 = w64 len ->
  WriterSpec.bytes_ok bs -> Z.of_nat (length bs) = len -> 0 <= len <= 2 ^ 27 ->
  zbytes_at tfibsegs W mem data bs -> 4096 <= data /\ data + len <= alloc_ceiling ->
  (0 < len -> exists kd, fs_rblock tfibsegs B ly S W mem data kd /\ len <= kd) ->
  fs_glob tfibsegs W mem live peak cnt fail ->
  st_nev S + EV_preset_base64_encode <= EV_MAX -> blocks_bytes S + (enc_size len + HEAD) <= LIVE_MAX ->
  live + enc_size len < 2 ^ 64 -> cnt + 1 < 2 ^ 64 ->
  encE_KLOOP ly S U W regs mem md data len bs live peak cnt fail ->
  encE_KTAIL ly S U W regs mem md data len bs live peak cnt fail ->
  SRr tfibsegs W (cfg_at tfibsegs A_preset_base64_encode regs mem md)
    (encE_post ly S U W regs mem md data len bs live peak cnt fail).
Proof.
intros ly S U W regs mem md ch data len bs live peak cnt fail HPRE FH HFRL H10 H11 HBS HBSL HLN HZB HD HRB HGL HEV
  HLV HLIVE HCNT KLOOP KTAIL.
apply (encE_spine ly S U W regs mem md ch len live peak cnt fail _ HPRE FH H11 HLN HGL HEV HLV HLIVE HCNT).
- intros W' ly' S' regs' mem' md' Hcf HRES H10' Hbl' HG'.
  eapply SRr_mono;
    [exact (encE_null ly S U W regs mem md ch live peak cnt W' ly' S' regs' mem' md' HPRE HCNT HRES H10' Hbl' HG')|].
  intros W2 c2 _ HP. left. split; [exact Hcf | exact HP].
- intros q W' ly' S' regs' mem' md' Hcf HRES H10' Hq Hbl' HH' Hrb HG'.
  exact (encE_succ ly S U W regs mem md ch data len bs live peak cnt fail q W' ly' S' regs' mem' md' HPRE H10 H11 HBS
    HBSL HLN HZB HD HRB KLOOP KTAIL Hcf HRES H10' Hq Hbl' HH' Hrb HG').
Qed.

(* ---- encode_spec, from the two continuations at every pre-call state ---- *)
Theorem encE_encode_spec :
  (forall ly S U W regs mem md data len bs live peak cnt fail,
     encE_KLOOP ly S U W regs mem md data len bs live peak cnt fail) ->
  (forall ly S U W regs mem md data len bs live peak cnt fail,
     encE_KTAIL ly S U W regs mem md data len bs live peak cnt fail) ->
  encode_spec B tfibsegs.
Proof.
intros KL KT. unfold encode_spec.
intros ly S U W regs mem md ch data len bs live peak cnt fail HPRE FH HFRL H10 H11 HBS HBSL HLN HZB HD HRB HGL HEV HLV
  HLIVE HCNT.
exact (encE_entry ly S U W regs mem md ch data len bs live peak cnt fail HPRE FH HFRL H10 H11 HBS HBSL HLN HZB HD HRB
  HGL HEV HLV HLIVE HCNT (KL ly S U W regs mem md data len bs live peak cnt fail)
  (KT ly S U W regs mem md data len bs live peak cnt fail)).
Qed.
End E.

About encE_entry.
About encE_encode_spec.
About encE_KLOOP.
About encE_KTAIL.
Print Assumptions encE_encode_spec.
