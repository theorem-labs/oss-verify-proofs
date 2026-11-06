(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/B/Prog/LLVMFuzzerTestOneInput_segX_exit_td.v, with its module paths, module names and numbers changed; 1110 of its 1140 lines of code are new or changed and 322 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/PSB_Tail.v, with its module names changed; 1182 of its 1298 lines of code are new or changed and 1024 lines of the source are left out. *)
(* fuzz_preset lib/B, parse_string on image B (asan-ubsan): the stretch PSB_SCAN (offset 148) .. PSB_DEC (offset 324),
   against the cut layer lib/A/Prog/PS_Gen.v + lib/B/Prog/PSB_Base.v on the kit's cut 7cdbb61b5fa0 (earlier the OLD-PIN
   ACCEPTANCE base 1ecd17746af on a working branch).
   rule 24: proves no function (kind: segment lemma). The function is parse_string B (lane BParseString); its reuse
   search is the record file r24-index.txt (sha256 e7c12b08eeb1; internal record) (checker CONFIRM; donor none).
   FILE SET: the kit's cut 7cdbb61b5fa0 with this row's lane files; at ACC-BRIEF, the acceptance base 6225fcbb328 on
   a working branch (PS_Gen blob 1ed8831ad889: ps_carryP / ps_postP / ps_at_ret0P, ps_rpos,
   srr_inv_laws_True / srr_inv_call_True; PSB_Base 37dbe86f11d0: psb_at_scanP / psb_at_decP, psb_seg_{scan,ret0,dec}P
   and their _of_True; PSB_Src 7630d0babd39: the text across the call); the OLD-PIN kit of record
   a working branch 4f18c75d4900 (owner 14:00Z; PRH_FnAlloc blob f668aebf57c4: tfuzz_malloc_specX
   takes the room position iface_room_pos and posts fpostm with the advanced position; PRH_Base ee6c7a38d6b6: fpre with
   the stack-top and raZ conjuncts, fQmn / fpostm at :689-697; PRH_FnReader 66e11f202508; YGcfRoomLive db11c2a5eb11);
   a Theorem Labs lane's image-B harness contract lib/AU/PresetCfnB.v (blob 395e15521a77: counts_of_room_pos_rl); the whole engine
   set s1b from a working branch 459129c18903 (YCbqG c3b5d0111037, YGcallcf 6d2b13c24437, YC80x
   14f84f225e8f: srr_inv_laws and the SRr _inv runners; YC1fPx 7814b594066f: paj_run_x_inv / paj_run_to_x_inv and their
   tactics; YSRrMemnorm 5ffa8525936b: srr_inv_call; YAkMemnorm 96c72061b4d4); listing v4 (B Listing_prog f843fdf7fe2f /
   PAImg_prog 5abade432081); PRW_StepKit f5da83bd521e / PRW_HShadow 2662d68ca36b. This file by path from
   a working branch 22a4423dbc1 (the generic-P walk), ported to the m-form callee text.
   THE GENERIC-P FORM (a Theorem Labs lane 12:18Z / 12:22Z; GP-BRIEF): an SRr post is OPAQUE once Qed, so the end-state invariant
   is in the stretch's statement. The walk (Section scP) is over an ABSTRACT invariant P of the memory with
   srr_inv_laws segs P (PLAW) and, since it crosses the fuzz_malloc call, srr_inv_call segs P (PCALL): the cut's P mem
   (ps_carryP's last conjunct) is the invariant premise of every engine run (YC1fPx's twins paj_run_x_inv /
   paj_run_to_x_inv at P with PLAW), which hands it back at the run's end memory; a branch keeps the state, so P stands.
   The exits put it in ps_carryP: the loop head (psc_loop), PSB_RET0 (the refused scan, psc_loop; the two refusing
   allocator arms, psc_final) and PSB_DEC (psc_final). Across `jal fuzz_malloc` the callee text's m-form post (fpostm:
   the post body at fQmn memc, so `memnorm memc -> memnorm mem2` at every post state) is CITED, and PCALL turns it into
   `P memc -> P mem2`. memnorm is never instantiated here.
   WHAT MOVED AND WHY: only the callee TEXT moved, never the invariant. (1) Kit preset-tree-at-2026-10-29T11-52-53Z.tsv (sha256 7a1c7c129aef; internal record) (ACC-BRIEF): fuzz_malloc's
   post is m-form and fpre asks raZ regs < YM05.alloc_ceiling, so the P theorem LOST its keep premise psc_malloc_mn and
   the walk's argument psc_malloc_P (the keep is the text's now); the call step psc_malloc_text states fpostm and takes
   raZ, which the call site discharges from the jal's return pc (a listing slot: below 2 ^ 46 by vm_compute, below
   CEIL_MIN by alloc_ceiling_value). (2) Kit preset-tree-at-2026-10-29T13-54-32Z.tsv (sha256 14e543909afe; internal record) (owner 14:00Z): tfuzz_malloc_specX takes the room position and
   posts the advanced one, so the open premise psc_rpos_after is DELETED (the post's conjunct gives ps_rpos D S'), and
   the two live counts at the call (S = pi_S D) come from ps_pre's iface_room_pos by PresetCfnB.counts_of_room_pos_rl
   (the route the kit's texts name). The theorems are renamed for it: psb_scan_holdsP (was psb_scan_holds_cntP) and the
   P := (fun _ => True) corollary psb_scan_holds (was psb_scan_holds_cnt), whose statement is now PSB_Base's
   psb_seg_scan with only the other stretches as hypotheses. Consumer: BParseString's top (told).
   (3) #102 RE-FIT (lane PstrBp, a working branch; relocated to B' d663f82d by alreloc c4338d099cfb8025): kit
   texts (PRH_FnAlloc 740f4d11d144): tfuzz_malloc_specX takes NO position and posts the
   POST-IMPLICATION (res = 0 transfers any position by [], res <> 0 by [HMal (n + cf_head)]), so psc_malloc_KC and
   psc_post_call carry the two implications; the two live counts at the call are ps_pre's peak premises over the
   all-granted events (PS_Gen.ps_counts_entry), so PresetCfnB.counts_of_room_pos_rl is no longer cited; the ledger
   takes `most own` (psc_ledger_low transports the g_most / g_own_ran_out cells); IMGV is psb_img_shadow_vis (image B's
   own pa_lo / pa_hi, PSB_Src.v), never YImgTop's IMG_LO / IMG_TOP.
   THE CODE (neutral listing parse_string.fuzz_preset.asan-ubsan.s (sha256 549ddc2d23bf; internal record); DERIVED offsets from the
   entry):
     148 srli/add/lb/bnez  the shadow check of the byte at the cursor (to 204, the partial-granule test, else 212
                           errpath_load1): NOT TAKEN, the engine's shadow obligation, discharged from src_rd's
                           range_addressable (psc_loop / psc_found, first run)
     164 lbu; 168 beq 34   the closing quote: to 216 (psc_found); else
     172..188              a3 = (c == 92) + 1; `not a4, a0; bltu a4, a3` to unimp (1372): NOT TAKEN (psc_wrap_ok)
     192 add; 196 bltu     back to 148 (the induction: psc_loop on text + len - x), else 200 `j 1256`: the scan
                           refuses (PjGrammar.scan = None), PSB_RET0
     216 sub; 220 addi     a0 = x - p = Q + 1 (psc_len_U); 224 `jal fuzz_malloc`: the ONE call step psc_malloc_text
                           through YCbqGcall.v aj_call_x_sp (the callee's chain: PS_Gen ps_chain_call_offq)
     228 beqz a0           the two refusing arms to PSB_RET0 (psc_post_call)
     236 lbu 0(s8); 240 bnez  the q + 8 shadow re-check (to 1416 errpath_load8): NOT TAKEN, the byte is 0 by ARx's
                           stack-shadow law alx_zshadow_byte at the post state (psa_entry's first region)
     244 ld a0, 0(s1); 248 bgeu s4, a0  to PSB_FREE: NOT TAKEN, p + 1 < end (psc_post_call)
     252..320              the decode constants, the three surrogate words at sp + 24 / 8 / 16, s3 = s2; 324 PSB_DEC
   OPEN PREMISES: none. The call step's premises are the call state's (fpre, the ledger, n = Q + 1) or the entry's
   (room_live_cf, the two peak counts, prh_univ_closure, the LIVE bound of ps_pre).
   Numerals: offsets 148 .. 1372 in comments and PSC_RET = 228 (DERIVED: byte offsets inside parse_string); 34, 92
   (WORD: the quote and the backslash); the decode constants 34, -1, 92, 32, 101, 91, 113, 114 and the surrogate words
   55296, 56320, -56613888 (WORD: the listing's li / lui immediates; 2 ^ 64 - 56613888 and 2 ^ 64 - 1 their 64-bit
   unsigned forms); register numbers 1 .. 27 and atom indices 0 .. 32, 240, 512, 513 (DERIVED: the engine's
   numbering); 1, 8, 16, 24, 32, 40, 144, 255, 256, 4096, 2 ^ 40, 2 ^ 44, 2 ^ 46, 2 ^ 47, 2 ^ 64, 4 (LENGTH: bytes,
   granule, struct pj_in, the frame, a byte's range, the image / shadow / stack bands, log2 of the stack alignment).
   No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YI16 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YGcfNames YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YC1fPx YCbqGcall YCbqGcallW.
(* srr_inv_laws and the runner twins are YC80x's / YC1fPx's since the s1b collapse (preset-tree-at-2026-10-29T12-55-44Z.tsv (sha256 7967f42d1cd6; internal record)); srr_inv_call is
   YSRrMemnorm.v's (5ffa8525936b; Requires YAkMemnorm only: no LiaTwx2 `lia ::=`) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnAlloc PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Charge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_StepKit PS_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PSB_Base PSB_Src.
(* the live counts at the call are ps_pre's peak premises (PS_Gen.ps_counts_entry, the post-implication form): no
   room position, so no harness contract (PresetCfnB's counts_of_room_pos_rl) is needed *)
(* the PLAIN build's sink instance is loaded transitively; it must never fill an ASan sink argument *)
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- THE MODEL SIDE: PjGrammar.scan over rest_atR (the released plain proof's statements, lib/Prog/
   parse_string_loops.v psl_rest_cons / psl_rest_end / psl_scan_q / psl_seqz; proved here over this engine) ---- *)
Lemma psc_rest_cons : forall tb text x c, text <= x -> nth_error tb (Z.to_nat (x - text)) = Some c ->
  rest_atR tb text x = c :: rest_atR tb text (x + 1).
Proof.
  intros tb text x c Hx Hc. unfold rest_atR.
  assert (Hs : forall (l : list Z) k v, nth_error l k = Some v -> skipn k l = v :: skipn (S k) l).
  { intros l. induction l as [|h t IH]; intros k v H; destruct k; cbn in *; try discriminate.
    - injection H as ->. reflexivity.
    - apply IH. exact H. }
  rewrite (Hs tb _ c Hc).
  replace (Z.to_nat (x + 1 - text)) with (S (Z.to_nat (x - text))) by lia. reflexivity.
Qed.
Lemma psc_rest_end : forall tb text x, Z.of_nat (length tb) <= x - text -> rest_atR tb text x = [].
Proof. intros tb text x Hx. unfold rest_atR. apply skipn_all2. lia. Qed.

(* one turn of the loop, on the model: the cursor moves by 1, or by 2 after a backslash *)
Lemma psc_step_scan : forall tb text x c,
  text <= x -> nth_error tb (Z.to_nat (x - text)) = Some c -> c <> 34 ->
  PjGrammar.scan (rest_atR tb text x) =
  option_map (fun Q => (Q + Z.to_nat ((if Z.eqb c 92 then x + 2 else x + 1) - x))%nat)
             (PjGrammar.scan (rest_atR tb text (if Z.eqb c 92 then x + 2 else x + 1))).
Proof.
  intros tb text x c Hx Hc H34. rewrite (psc_rest_cons tb text x c Hx Hc).
  destruct (Z.eqb_spec c 92) as [E92|E92].
  - subst c. destruct (nth_error tb (Z.to_nat (x + 1 - text))) as [e|] eqn:He.
    + rewrite (psc_rest_cons tb text (x + 1) e ltac:(lia) He), PjGrammar.scan_bs.
      replace (x + 1 + 1) with (x + 2) by lia.
      destruct (PjGrammar.scan (rest_atR tb text (x + 2))) as [Q|]; cbn [option_map]; [|reflexivity].
      f_equal. lia.
    + apply nth_error_None in He.
      rewrite (psc_rest_end tb text (x + 1)) by lia. rewrite (psc_rest_end tb text (x + 2)) by lia.
      reflexivity.
  - rewrite (PjGrammar.scan_ndq c _ H34 E92).
    destruct (PjGrammar.scan (rest_atR tb text (x + 1))) as [Q|]; cbn [option_map]; [|reflexivity].
    f_equal. lia.
Qed.

(* the machine's step a3 = (c == 92) + 1 *)
Lemma psc_seqz : forall c, 0 <= c < 256 ->
  zalu_raw 63 64 ALU_SLTU (zcanon (c + -92)) (zcanon 1) = if c =? 92 then 1 else 0.
Proof.
  intros c Hc. cbn [zalu_raw]. unfold zcanon, M64.
  change (1 mod 2 ^ 64) with 1.
  destruct (Z.eqb_spec c 92) as [E|E].
  - rewrite E. change ((92 + -92) mod 2 ^ 64) with 0. reflexivity.
  - replace ((c + -92) mod 2 ^ 64 <? 1) with false; [reflexivity|].
    symmetry. apply Z.ltb_ge. Z.div_mod_to_equations. lia.
Qed.

(* `not a4, a0` of a cursor below 2 ^ 64: 2 ^ 64 - 1 - x *)
Lemma psc_lxor_ones : forall x, 0 <= x < 2 ^ 64 -> Z.lxor x (2 ^ 64 - 1) = 2 ^ 64 - 1 - x.
Proof.
  intros x Hx. replace (2 ^ 64 - 1) with (Z.ones 64) by reflexivity.
  assert (H0 : Z.ldiff x (Z.ones 64) = 0).
  { apply Z.bits_inj'. intros m Hm. rewrite Z.ldiff_spec, Z.testbit_ones_nonneg by lia. rewrite Z.bits_0.
    destruct (Z.ltb_spec m 64); [cbn; apply andb_false_r|].
    replace (Z.testbit x m) with false; [reflexivity|].
    rewrite <- (Z.mod_small x (2 ^ 64)) by lia. symmetry. apply Z.mod_pow2_bits_high. lia. }
  rewrite (Z.sub_nocarry_ldiff (Z.ones 64) x H0).
  apply Z.bits_inj'. intros m Hm. rewrite Z.lxor_spec, Z.ldiff_spec, Z.testbit_ones_nonneg by lia.
  destruct (Z.ltb_spec m 64).
  - destruct (Z.testbit x m); reflexivity.
  - replace (Z.testbit x m) with false; [reflexivity|].
    rewrite <- (Z.mod_small x (2 ^ 64)) by lia. symmetry. apply Z.mod_pow2_bits_high. lia.
Qed.

(* the turn's step a3 = (c == 92) + 1, as the engine's symbolic value *)
Lemma psc_step_U : forall E c, ew E 32 = Z_to_bv 64 c -> 0 <= c < 256 ->
  U E (SAlu ALU_ADD (SAlu ALU_SLTU (SOff 32 (-92)) (SLit 1)) (SLit 1)) = (if c =? 92 then 1 else 0) + 1.
Proof.
  intros E c E32 Hc. rewrite !U_SAlu, !U_SLit, (U_SOff E 32), E32.
  rewrite (unsigned_lit_small c) by lia. rewrite (psc_seqz c Hc).
  rewrite (zcanon_id (if c =? 92 then 1 else 0)) by (destruct (c =? 92); unfold M64; lia).
  rewrite (zcanon_id 1) by (unfold M64; lia). cbn [zalu_raw].
  apply zcanon_id. destruct (c =? 92); unfold M64; lia.
Qed.

(* the UBSan pointer-wrap check `not a4, a0; bltu a4, a3` (offsets 184 / 188): NOT TAKEN, the cursor is below 2 ^ 47 *)
Lemma psc_wrap_ok : forall E c x, ew E 32 = Z_to_bv 64 c -> ew E 10 = Z_to_bv 64 x -> 0 <= c < 256 -> 0 <= x < 2 ^ 47 ->
  (U E (SAlu ALU_XOR (SOff 10 0) (SLit (-1))) <?
   U E (SAlu ALU_ADD (SAlu ALU_SLTU (SOff 32 (-92)) (SLit 1)) (SLit 1))) = false.
Proof.
  intros E c x E32 E10 Hc Hx. rewrite (psc_step_U E c E32 Hc).
  rewrite U_SAlu, U_SLit, (U_SOff E 10), E10. rewrite (unsigned_lit_small x) by lia.
  rewrite Z.add_0_r, (zcanon_id x) by (unfold M64; lia).
  change (zcanon (-1)) with (2 ^ 64 - 1). cbn [zalu_raw]. rewrite (psc_lxor_ones x) by lia.
  rewrite zcanon_id by (unfold M64; lia).
  apply Z.ltb_ge. destruct (c =? 92); lia.
Qed.

(* the machine's next cursor `add a0, a0, a3` (offset 192) is exactly the model's: x + (c == 92) + 1 *)
Lemma psc_next_U : forall E c x, ew E 32 = Z_to_bv 64 c -> ew E 10 = Z_to_bv 64 x -> 0 <= c < 256 -> 0 <= x < 2 ^ 47 ->
  U E (SAlu ALU_ADD (SOff 10 0) (SAlu ALU_ADD (SAlu ALU_SLTU (SOff 32 (-92)) (SLit 1)) (SLit 1)))
  = if c =? 92 then x + 2 else x + 1.
Proof.
  intros E c x E32 E10 Hc Hx. rewrite U_SAlu, (psc_step_U E c E32 Hc), (U_SOff E 10), E10.
  rewrite (unsigned_lit_small x) by lia. rewrite Z.add_0_r, (zcanon_id x) by (unfold M64; lia).
  cbn [zalu_raw]. rewrite zcanon_id by (destruct (c =? 92); unfold M64; lia).
  destruct (c =? 92); lia.
Qed.
Lemma psc_next_cursor : forall E c x, ew E 32 = Z_to_bv 64 c -> ew E 10 = Z_to_bv 64 x -> 0 <= c < 256 ->
  0 <= x < 2 ^ 47 ->
  sv_denot E (SAlu ALU_ADD (SOff 10 0) (SAlu ALU_ADD (SAlu ALU_SLTU (SOff 32 (-92)) (SLit 1)) (SLit 1)))
  = w64 (if c =? 92 then x + 2 else x + 1).
Proof.
  intros E c x E32 E10 Hc Hx. rewrite denot_lit_U. unfold w64. f_equal. exact (psc_next_U E c x E32 E10 Hc Hx).
Qed.

(* the length the code passes to fuzz_malloc, `sub a0, a0, s4; addi a0, a0, 1` (offsets 216 / 220): x - (p + 1) + 1 *)
Lemma psc_len_U : forall E x p, ew E 10 = Z_to_bv 64 x -> ew E 20 = Z_to_bv 64 (p + 1) -> 0 <= p -> p + 1 <= x < 2 ^ 47 ->
  U E (SAlu ALU_ADD (SOff 10 1) (SMd M_MUL (SOff 20 0) (SLit (2 ^ 64 - 1)))) = x - p.
Proof.
  intros E x p E10 E20 Hp Hx. rewrite U_SAlu, U_SMd, U_SLit, (U_SOff E 10), (U_SOff E 20), E10, E20.
  rewrite (unsigned_lit_small x), (unsigned_lit_small (p + 1)) by lia.
  rewrite Z.add_0_r. rewrite (zcanon_id (x + 1)), (zcanon_id (p + 1)) by (unfold M64; lia).
  rewrite (zcanon_id (2 ^ 64 - 1)) by (unfold M64; lia). cbn [zmd_raw zalu_raw].
  unfold zcanon, M64.
  replace ((p + 1) * (2 ^ 64 - 1)) with ((2 ^ 64 - (p + 1)) + p * 2 ^ 64) by ring.
  rewrite Z_mod_plus_full, (Z.mod_small (2 ^ 64 - (p + 1))) by lia.
  replace (x + 1 + (2 ^ 64 - (p + 1))) with ((x - p) + 1 * 2 ^ 64) by ring.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

(* ---- THE SYMBOLIC STATE AT THE LOOP HEAD (offset 148). Atoms: 0..31 the current registers (10 = a0 = x the cursor,
   12 = a2 = 34, 23 = s7 = the shadow base), 32 = the byte at x (one extra word of the environment). The one region
   is the single text byte the turn reads; it is READ-ONLY (wlo = whi = 0). ---- *)
Definition PSC_Bx : sv := SOff 23 0.
Definition PSC_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition psc_regions : smem := [ YP09.mkRegion (Some 10%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))] ].
Definition psc_facts : facts :=
  mkFacts [(10%nat, mkAF 4096 (2 ^ 47 - 1) 0); (32%nat, mkAF 0 255 0); (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_psc : sstate := mkSS (PSB_OFF + PSB_SCAN) sr_atoms psc_regions None psc_facts.
(* ---- THE SYMBOLIC STATE AFTER THE CALL (offset 228, the return point of `jal fuzz_malloc` at 224). Atoms: 0..31 the
   registers after the call (10 = a0 = the result, 24 = s8 = the shadow cell of q + 8, 9 = s1 = q + 8, 2 = sp), 32 =
   text + len (one extra word). Regions: the shadow byte of q + 8 (read-only, 0), the end word at q + 8 (read-only),
   and the three surrogate slots sp + 8 .. sp + 32 of the frame (writable). ---- *)
(* DERIVED: the byte offset of the instruction after `jal fuzz_malloc` (224 + 4) *)
Definition PSC_RET : Z := 228.
Definition psa_regions : smem :=
  [ YP09.mkRegion (Some 24%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))];
    YP09.mkRegion (Some 9%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))];
    YP09.mkRegion (Some 2%nat) 8 32 8 32 [] ].
Definition psa_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
Definition ss_psa : sstate := mkSS (PSB_OFF + PSC_RET) sr_atoms psa_regions None psa_facts.


Section psc. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
(* image B's instances (PSB_Base.v's), the ones the engine's tactics infer; every statement below names them *)
#[local] Existing Instances PSB_PrhImg PSB_PAListing PSB_PAImg.
#[local] Notation segs := (@pa_segs _ B_prog_listing PSB_PAImg).
#[local] Notation VAL := (@pa_val _ B_prog_listing PSB_PAImg).
#[local] Notation BASE := (@pa_val _ B_prog_listing PSB_PAImg A_TEXT).
#[local] Notation EB := (Eimg (L := B_prog_listing) (PI := PSB_PAImg)).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
#[local] Notation PST := (prh_pst (PI := PSB_PrhImg)).
#[local] Notation AJ := (ajournal_x (SK := SK) segs B PST ARx).
#[local] Notation KEPT := (cj_kept (SK := SK) segs B PST).
#[local] Notation LEDGER := (prh_ledger (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg) B).
#[local] Notation ps_in := (ps_in (L := B_prog_listing) (PA := PSB_PAImg)).
#[local] Notation PS_SP := (PS_SP (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg)).
#[local] Notation ps_pre := (ps_pre (RL := RL) (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg) B ARx).
#[local] Notation ps_Qres := (ps_Qres (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg) B).
#[local] Notation ps_gptp := (ps_gptp (L := B_prog_listing) (PA := PSB_PAImg)).
#[local] Notation ps_x := (ps_x (L := B_prog_listing) (PA := PSB_PAImg)).
#[local] Notation PS_FRAME := (PS_FRAME (PI := PSB_PrhImg)).
#[local] Notation ps_rpos := (ps_rpos (L := B_prog_listing) (PA := PSB_PAImg)).
#[local] Notation ps_rpos_mal := (ps_rpos_mal (L := B_prog_listing) (PA := PSB_PAImg)).

(* ---- the Section hypotheses (the internal file STRETCH-BRIEF.md; ZSA / IMGV by BParseString's agreement, S4_PsSrc.v's text) ---- *)
Hypothesis LAWS : AR_laws_x segs B ARx cf_head.
Hypothesis TL : PALib (L := B_prog_listing) (PI := PI_prog_B) B.
Hypothesis PST_ok : forall a, Exists (in_zr a) prh_pst -> in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B).
Hypothesis HMALLOC : tfuzz_malloc_specX B ARx SK.
Hypothesis ZSA : forall q m, In (q, m) (as_zero_shadow B) -> q mod 8 = 0 /\ m mod 8 = 0.
Hypothesis IMGV : psb_img_shadow_vis ARx.

(* a refused scan makes no allocator event, so the walk's charge is 0 *)
Lemma psc_held_none : forall x, PjGrammar.scan x = None ->
  PRH_Charge.prh_held (PRH_Charge.prhPs_gtrace x) = 0.
Proof.
  intros x H. unfold PRH_Charge.prh_held, PRH_Charge.prhPs_gtrace, PjGrammar.jr_string.
  rewrite H. cbn. lia.
Qed.

Definition PSC_E (regs : bvmap 5 word) (c : Z) : env := EB (Ereg regs [Z_to_bv 64 c]).

Lemma psc_ew_reg : forall regs c n (r : bv 5), Z.of_nat n = bv_unsigned r -> (n < 32)%nat ->
  ew (PSC_E regs c) n = getr regs r.
Proof.
  intros regs c n r Hn H32. unfold PSC_E. rewrite Eimg_low by (unfold A_TEXT; lia).
  exact (ew_Ereg_nat regs _ n r Hn).
Qed.
Lemma psc_ew_byte : forall regs c, ew (PSC_E regs c) 32 = Z_to_bv 64 c.
Proof.
  intros regs c. unfold PSC_E. rewrite Eimg_low by (unfold A_TEXT; lia).
  replace 32%nat with (32 + 0)%nat by lia. rewrite ew_Ereg_extra. reflexivity.
Qed.

(* ==== THE WALK OVER THE INVARIANT (GP-BRIEF; a Theorem Labs lane 12:18Z): P abstract, with its runner laws PLAW. Every cut is
   taken in its P form (psb_at_scanP / ps_at_ret0P / psb_at_decP: ps_carryP with P mem last); the goal is ps_postP. ==== *)
Section scP.
Variable P : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws segs P.
(* the stretch crosses the fuzz_malloc call: P follows the callee text's memnorm keep (YSRrMemnorm 5ffa8525936b) *)
Hypothesis PCALL : srr_inv_call segs P.
#[local] Notation ps_carryP := (ps_carryP (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg) B ARx SK P).
#[local] Notation ps_postP := (ps_postP (RL := RL) (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg) B ARx SK P).
(* the hand-off form (PS_Gen): the pieces run at wle into the SRr' fact of the stretch they hand to; the decode
   stretch may cross the bad escape's fuzz_free (ps_finP_hand), the NULL return ends at wle (ps_finP_of_postP) *)
#[local] Notation ps_finP := (ps_finP (RL := RL) (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg) B ARx SK P).

(* the entry state of one turn: the symbolic state at offset 148 and the (empty) shadow-entry list *)
Lemma psc_entry : forall (D : ps_in) ly S Hp W regs mem md x c,
  psb_at_scanP B ARx SK P D ly S Hp W regs mem md x ->
  nth_error (pi_tb D) (Z.to_nat (x - pi_text D)) = Some c ->
  st_ok_pi segs VAL (PSC_E regs c) ss_psc
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (PSB_OFF + PSB_SCAN))) mem (seg_rom segs)))
  /\ sh_ok segs PSC_Bx [] (PSC_E regs c) (mrestrict (w_H W) mem).
Proof.
intros D ly S Hp W regs mem md x c HAT Hc.
pose proof HAT as (HC & HSH & _ & _ & _ & _ & _ & _ & HPJ & _ & _ & R10 & _ & R12 & _ & _ & _ & Hx & _).
pose proof HC as (_ & _ & _ & HSRC & _).
pose proof HSH as (R23 & _ & _).
pose proof HSRC as (HBY & Htext0 & Hceil & Hamr & _ & _).
pose proof HPJ as (_ & _ & _ & _ & _ & Htpos & Htlen & Hple & Hlen & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hj : (Z.to_nat (x - pi_text D) < length (pi_tb D))%nat)
  by (apply nth_error_Some; rewrite Hc; discriminate).
assert (Hnth : nth (Z.to_nat (x - pi_text D)) (pi_tb D) 0 = c)
  by (rewrite (nth_error_nth _ _ 0 Hc); reflexivity).
destruct (HBY (Z.to_nat (x - pi_text D)) Hj) as [HV HR]. rewrite Hnth in HV, HR.
replace (pi_text D + Z.of_nat (Z.to_nat (x - pi_text D))) with x in HV by lia.
assert (Hxlo : 4096 <= x) by lia.
assert (Hxhi : x <= 2 ^ 47 - 1) by lia.
rewrite restrict_mkst_fx.
set (E := PSC_E regs c) in *.
assert (E10 : ew E 10 = w64 x) by (subst E; rewrite (psc_ew_reg regs c 10 10%bv eq_refl ltac:(lia)); exact R10).
assert (E23 : ew E 23 = w64 SHADOW_OFF) by (subst E; rewrite (psc_ew_reg regs c 23 23%bv eq_refl ltac:(lia)); exact R23).
assert (E32 : ew E 32 = Z_to_bv 64 c) by (subst E; apply psc_ew_byte).
assert (U10 : bv_unsigned (ew E 10) = x) by (rewrite E10; unfold w64; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E 23) = SHADOW_OFF) by (rewrite E23; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew E 32) = c) by (rewrite E32; apply unsigned_lit_small; lia).
split.
- unfold ss_psc. apply pa_entry_st_ok_full.
  + subst E. unfold PSC_E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold psc_regions. apply Forall_cons; [|apply Forall_nil].
    unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U10. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs E _ x 0 1 (SOff 32 0) c).
    * cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    * cbn. lia.
    * cbn. lia.
    * rewrite Z.add_0_r. exact HV.
  + exact (conj I I).
  + split; [|split; [exact I | exact I]].
    cbn [psc_facts f_atoms atoms_ok].
    split; [|split; [|split; [|exact I]]]; unfold afact_ok; cbn [af_lo af_hi af_al2].
    * rewrite U10. rewrite Z.pow_0_r, Z.mod_1_r. lia.
    * rewrite U32. rewrite Z.pow_0_r, Z.mod_1_r. lia.
    * rewrite U23. rewrite Z.pow_0_r, Z.mod_1_r. lia.
- unfold sh_ok. apply Forall_nil.
Qed.

(* the two atom values the engine's obligations speak of: the shadow base and the cursor *)
Lemma psc_U_Bx : forall (D : ps_in) regs c, psb_sh_regs D regs -> U (PSC_E regs c) PSC_Bx = SHADOW_OFF.
Proof.
intros D regs c (R23 & _ & _). unfold PSC_Bx. apply (U_atom _ 23 SHADOW_OFF).
- rewrite (psc_ew_reg regs c 23 23%bv eq_refl ltac:(lia)). exact R23.
- unfold SHADOW_OFF. lia.
Qed.
Lemma psc_U_x : forall regs c x, getr regs 10 = w64 x -> 0 <= x < 2 ^ 64 ->
  U (PSC_E regs c) (SOff 10 0) = x.
Proof.
intros regs c x R10 Hx. apply (U_atom _ 10 x); [|exact Hx].
rewrite (psc_ew_reg regs c 10 10%bv eq_refl ltac:(lia)). exact R10.
Qed.

(* a run that writes nothing leaves the memory alone *)
Lemma psc_frame_id : forall E rs (m m' : word -> option byte),
  frame_of E rs m m' -> (forall r, In r rs -> YP09.r_whi r <= YP09.r_wlo r) -> m' = m.
Proof.
intros E rs m m' HF Hro. apply functional_extensionality. intros y. apply HF.
intros (r & Hin & Ha). pose proof (Hro r Hin). lia.
Qed.
(* the environment the two shadow-check atoms extend: every atom of the entry env is kept *)
Lemma psc_ew_ext2 : forall regs c w0 w1 n, (n < 512)%nat ->
  ew (ewset (ewset (PSC_E regs c) 512 w0) 513 w1) n = ew (PSC_E regs c) n.
Proof. intros regs c w0 w1 n Hn. rewrite !ew_ewset_other by lia. reflexivity. Qed.
(* a register the turn leaves alone still holds its entry value *)
Lemma psc_reg_kept : forall (H : word -> bool) ss ms regs c w0 w1 (r : bv 5) n,
  st_ok_pi segs VAL (ewset (ewset (PSC_E regs c) 512 w0) 513 w1) ss (restrict H ms) ->
  sr_get (ss_regs ss) r = SOff n 0 -> Z.of_nat n = bv_unsigned r -> (n < 32)%nat ->
  getr (ms_regs ms) r = getr regs r.
Proof.
intros H ss ms regs c w0 w1 r n HS Hr Hn H32.
rewrite (st_ok_pi_restrict_reg H _ ss ms r HS), Hr.
rewrite (denot_lit_U _ (SOff n 0)), U_SOff, Z.add_0_r, psc_ew_ext2 by lia.
rewrite (psc_ew_reg regs c n r Hn H32). unfold zcanon, M64.
rewrite Z.mod_small by (pose proof (bv_unsigned_in_range 64 (getr regs r)) as Hb; unfold bv_modulus in Hb; lia).
apply Z_to_bv_bv_unsigned.
Qed.
(* the kept relation does not look at the materialised vm pages *)
Lemma psc_kept_wvb : forall STKf sp OR FPc lyc Sc W memc mdc ly2 S2 W2 mem2 md2 X,
  KEPT STKf sp OR FPc lyc Sc W memc mdc ly2 S2 W2 mem2 md2 ->
  KEPT STKf sp OR FPc lyc Sc W memc mdc ly2 S2 W2 mem2 (with_vm_backing (m_vm_lazy md2) X md2).
Proof.
intros STKf sp OR FPc lyc Sc W memc mdc ly2 S2 W2 mem2 md2 X (H1 & H2 & H3 & H4 & REST).
split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
split; [|exact REST].
eapply aos_step_same_io; [exact H4|]. apply same_io_materialized, same_but_materialized_wvb_any.
Qed.
Ltac psc_kr HS := eapply (psc_reg_kept _ _ _ _ _ _ _ _ _ HS); [vm_compute; reflexivity | reflexivity | lia].
(* a read-only run leaves the memory: the frame relation of the run with its one read-only region *)
Ltac psc_mem_id := eapply psc_frame_id; [eassumption | intros r Hin; cbn in Hin; destruct Hin as [<-|[]]; cbn; lia].
(* the machine state at a cut offset, read as the cut's configuration *)
Ltac psc_at off :=
  lazymatch goal with |- SRr _ ?Wg (mkCfg (YK11.mkst ?r (Z_to_bv 64 ?pcv) ?m _) ?d) ?Qg =>
    replace pcv with (psb_pc off) by (unfold psb_pc; vm_compute; reflexivity);
    change (SRr segs Wg (cfg_at segs (psb_pc off) r m d) Qg) end.

(* the found path (the byte at the cursor is the quote) *)
Definition psc_found_at (CTX : list (list Z)) (CW : list (list Z)) (D : ps_in) : Prop :=
  forall regs mem md x,
    psb_at_scanP B ARx SK P D (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) regs mem md x ->
    nth_error (pi_tb D) (Z.to_nat (x - pi_text D)) = Some 34 ->
    SRr segs (pi_W D) (cfg_at segs (psb_pc PSB_SCAN) regs mem md) (ps_finP CW D).

(* THE LOOP. The measure is the bytes left, text + len - x. *)
Lemma psc_loop : forall CTX CW (D : ps_in), psb_seg_ret0P B ARx SK CTX CW P -> ps_pre CTX CW D ->
  psc_found_at CTX CW D ->
  forall n x regs mem md, (Z.to_nat (pi_text D + pi_len D - x) <= n)%nat ->
  psb_at_scanP B ARx SK P D (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) regs mem md x ->
  SRr segs (pi_W D) (cfg_at segs (psb_pc PSB_SCAN) regs mem md) (ps_finP CW D).
Proof.
intros CTX CW D HRET0 HPRE HFOUND n. induction n as [|n IH]; intros x regs mem md Hn HAT.
{ exfalso. pose proof HAT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hx & _). lia. }
pose proof HAT as (HC & HSH & HGP & _ & _ & _ & _ & HLED & HPJ & HROD & R2 & R10 & R11 & R12 & R8 & R9 & R20 & Hx & Heq).
pose proof HC as (HJ & HKEPT & HSAVED & HSRC & HHOME & HMN).
pose proof HPJ as (_ & _ & _ & _ & _ & Htpos & Htlen & Hple & Hlen & _).
pose proof HSRC as (HBY & Ht4096 & Htceil & Htamr & HRA & _).
pose proof asan_consts as (C1 & _).
assert (Hx47 : x < 2 ^ 47) by lia.
assert (Hj : (Z.to_nat (x - pi_text D) < length (pi_tb D))%nat) by lia.
destruct (nth_error (pi_tb D) (Z.to_nat (x - pi_text D))) as [c|] eqn:Hbyte;
  [|apply nth_error_None in Hbyte; lia].
destruct (Z.eq_dec c 34) as [E34|E34]; [subst c; exact (HFOUND regs mem md x HAT Hbyte)|].
assert (HR256 : 0 <= c < 256).
{ destruct (HBY (Z.to_nat (x - pi_text D)) Hj) as [_ HR].
  rewrite (nth_error_nth _ _ 0 Hbyte) in HR. exact HR. }
destruct (psc_entry D (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) regs mem md x c HAT Hbyte) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (PSC_E regs c)) by (unfold PSC_E; apply Eimg_env).
(* the runner twins at the invariant P (laws PLAW): each run takes the cut's HMN : P mem and hands it back at its end *)
pose (RUN := @paj_run_x_inv fx rc SK _ PSB_PAListing PSB_PAImg B PST ARx _ LAWS P PLAW).
pose (RUNTO := @paj_run_to_x_inv fx rc SK _ PSB_PAListing PSB_PAImg B PST ARx _ LAWS P PLAW).
pose (BR := paj_branch (PI := PSB_PAImg)).
unfold cfg_at, psb_pc, w64. rewrite <- Z.add_assoc.
paj_run_tok_x_inv RUN HS HJ SHOK HMN PSC_Bspan.
- (* the shadow obligation of the turn's one byte: the text is addressable by src_rd *)
  cbn [ms_mem mkst]. rewrite (psc_U_Bx D regs c HSH), (psc_U_x regs c x R10 ltac:(lia)).
  eapply range_addressable_sub; [exact HRA | lia | lia].
- (* the write premise: the turn's one region is read-only *)
  unfold ss_psc, psc_regions. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil].
- (* at the `beq a3, a2` of offset 168 *)
  assert (Emem : ms_mem ms = mem).
  { eapply psc_frame_id; [exact HF|].
    intros r Hin. unfold ss_psc, psc_regions in Hin. cbn in Hin.
    destruct Hin as [<-|[]]. cbn. lia. }
  psrr_branch_tok RUN BR HS SHOK PSC_Bspan.
  + (* the quote: excluded, the byte is not 34 *)
    exfalso. rewrite branch_eq_U in Hc.
    rewrite (U_atom _ 32 c), (U_atom _ 12 34) in Hc.
    * apply Z.eqb_eq in Hc. exact (E34 Hc).
    * rewrite psc_ew_ext2 by lia. rewrite (psc_ew_reg regs c 12 12%bv eq_refl ltac:(lia)). exact R12.
    * lia.
    * rewrite psc_ew_ext2 by lia. apply psc_ew_byte.
    * lia.
  + (* not the quote: to the UBSan wrap check `bltu a4, a3` of offset 188 *)
    clear Hc. paj_run_tok_x_inv RUN HS HJ SHOK HMN PSC_Bspan.
    * intros a (r & Hin & Ha). cbn in Hin. destruct Hin as [<-|[]]. cbn in Ha. lia.
    * assert (E32' : ew (ewset (ewset (PSC_E regs c) 512 w) 513 w0) 32 = Z_to_bv 64 c)
        by (rewrite psc_ew_ext2 by lia; apply psc_ew_byte).
      assert (E10' : ew (ewset (ewset (PSC_E regs c) 512 w) 513 w0) 10 = Z_to_bv 64 x)
        by (rewrite psc_ew_ext2 by lia; rewrite (psc_ew_reg regs c 10 10%bv eq_refl ltac:(lia)); exact R10).
      psrr_branch_tok RUN BR HS SHOK PSC_Bspan.
      -- (* taken: the UBSan trap (unimp at 1372), excluded: the cursor does not wrap *)
         exfalso. rewrite branch_ltu_U, (psc_wrap_ok _ c x E32' E10' HR256 ltac:(lia)) in Hc. discriminate Hc.
      -- (* not taken: a0 = x + a3, to the loop test `bltu a0, a1` of offset 196 *)
         clear Hc. paj_run_tok_x_inv RUN HS HJ SHOK HMN PSC_Bspan.
         ++ intros a (r & Hin & Ha). cbn in Hin. destruct Hin as [<-|[]]. cbn in Ha. lia.
         ++ assert (Emem0 : ms_mem ms1 = mem).
            { rewrite <- Emem. eapply eq_trans; [psc_mem_id | psc_mem_id]. }
            pose proof (psc_next_U _ c x E32' E10' HR256 ltac:(lia)) as UA0.
            pose proof (psc_next_cursor _ c x E32' E10' HR256 ltac:(lia)) as DA0.
            remember (if c =? 92 then x + 2 else x + 1) as x' eqn:Ex'.
            try rewrite <- Ex' in UA0. try rewrite <- Ex' in DA0.
            assert (Hx' : x + 1 <= x' <= x + 2) by (rewrite Ex'; destruct (c =? 92); lia).
            assert (U11 : U (ewset (ewset (PSC_E regs c) 512 w) 513 w0) (SOff 11 0) = pi_text D + pi_len D).
            { apply U_atom; [|lia]. rewrite psc_ew_ext2 by lia.
              rewrite (psc_ew_reg regs c 11 11%bv eq_refl ltac:(lia)). exact R11. }
            (* the scan equation one step on: the model's step is the machine's *)
            pose proof (psc_step_scan (pi_tb D) (pi_text D) x c ltac:(lia) Hbyte E34) as Hstep.
            rewrite <- Ex' in Hstep.
            psrr_branch_tok RUN BR HS SHOK PSC_Bspan.
            ** (* taken: x' < text + len, back to the loop head at 148 *)
               rewrite branch_ltu_U, U11, UA0 in Hc. apply Z.ltb_lt in Hc.
               paj_run_to_tok_x_inv RUNTO HS HJ SHOK HMN PSC_Bspan (PSB_OFF + PSB_SCAN).
               +++ intros a (r & Hin & Ha). cbn in Hin. destruct Hin as [<-|[]]. cbn in Ha. lia.
               +++ assert (Emem2 : ms_mem ms2 = mem) by (rewrite <- Emem0; psc_mem_id).
                   pmkst HS. psc_at PSB_SCAN.
                   rewrite !wvb_collapse in HJ.
                   assert (K2 : getr (ms_regs ms2) 2%bv = getr regs 2%bv) by psc_kr HS.
                   assert (K3 : getr (ms_regs ms2) 3%bv = getr regs 3%bv) by psc_kr HS.
                   assert (K4 : getr (ms_regs ms2) 4%bv = getr regs 4%bv) by psc_kr HS.
                   assert (K8 : getr (ms_regs ms2) 8%bv = getr regs 8%bv) by psc_kr HS.
                   assert (K9 : getr (ms_regs ms2) 9%bv = getr regs 9%bv) by psc_kr HS.
                   assert (K11 : getr (ms_regs ms2) 11%bv = getr regs 11%bv) by psc_kr HS.
                   assert (K12 : getr (ms_regs ms2) 12%bv = getr regs 12%bv) by psc_kr HS.
                   assert (K20 : getr (ms_regs ms2) 20%bv = getr regs 20%bv) by psc_kr HS.
                   assert (K22 : getr (ms_regs ms2) 22%bv = getr regs 22%bv) by psc_kr HS.
                   assert (K23 : getr (ms_regs ms2) 23%bv = getr regs 23%bv) by psc_kr HS.
                   assert (K24 : getr (ms_regs ms2) 24%bv = getr regs 24%bv) by psc_kr HS.
                   assert (K10 : getr (ms_regs ms2) 10%bv = w64 x').
                   { rewrite (st_ok_pi_restrict_reg _ _ _ _ (10%bv : bv 5) HS). exact DA0. }
                   lazymatch goal with |- SRr _ _ (cfg_at _ _ _ _ ?mdq) _ =>
                     apply (IH x' (ms_regs ms2) (ms_mem ms2) mdq); [lia|] end.
                   rewrite Emem2 in HJ, HMN |- *.
                   unfold psb_at_scanP.
                   split.
                   { split; [exact HJ|]. split; [apply psc_kept_wvb; exact HKEPT|].
                     split; [exact HSAVED|]. split; [exact HSRC|]. split; [exact HHOME | exact HMN]. }
                   split; [unfold psb_sh_regs; rewrite K23, K22, K24; exact HSH|].
                   split; [unfold ps_gptp; rewrite K3, K4; exact HGP|].
                   split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
                   split; [exact HLED|]. split; [exact HPJ|]. split; [exact HROD|].
                   split; [rewrite K2; exact R2|]. split; [exact K10|].
                   split; [rewrite K11; exact R11|]. split; [rewrite K12; exact R12|].
                   split; [rewrite K8; exact R8|]. split; [rewrite K9; exact R9|].
                   split; [rewrite K20; exact R20|].
                   split; [lia|].
                   rewrite Heq, Hstep.
                   destruct (PjGrammar.scan (rest_atR (pi_tb D) (pi_text D) x')) as [Q|]; cbn [option_map]; [|reflexivity].
                   f_equal. lia.
            ** (* not taken: x' >= text + len, `j 1256`: the scan refuses; to PSB_RET0 *)
               rewrite branch_ltu_U, U11, UA0 in Hc. apply Z.ltb_ge in Hc.
               paj_run_to_tok_x_inv RUNTO HS HJ SHOK HMN PSC_Bspan (PSB_OFF + PSB_RET0).
               +++ intros a (r & Hin & Ha). cbn in Hin. destruct Hin as [<-|[]]. cbn in Ha. lia.
               +++ assert (Emem2 : ms_mem ms2 = mem) by (rewrite <- Emem0; psc_mem_id).
                   pmkst HS. psc_at PSB_RET0.
                   rewrite !wvb_collapse in HJ.
                   assert (K2 : getr (ms_regs ms2) 2%bv = getr regs 2%bv) by psc_kr HS.
                   assert (K3 : getr (ms_regs ms2) 3%bv = getr regs 3%bv) by psc_kr HS.
                   assert (K4 : getr (ms_regs ms2) 4%bv = getr regs 4%bv) by psc_kr HS.
                   assert (Hnone : PjGrammar.scan (ps_x D) = None).
                   { rewrite Heq, Hstep. rewrite (psc_rest_end (pi_tb D) (pi_text D) x') by lia. reflexivity. }
                   pose proof HPRE as (_ & _ & _ & _ & _ & _ & HRL & HRP & _).
                   apply ps_finP_of_postP. apply (HRET0 D (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) _ _ _ HPRE).
                   rewrite Emem2 in HJ, HMN |- *.
                   unfold ps_at_ret0P.
                   split.
                   { exists 0, []. split; [apply ps_wb_nil|]. split; [exact HJ|]. split; [apply psc_kept_wvb; exact HKEPT|].
                     split; [exact HSAVED|]. split; [exact HSRC|]. split; [exact HHOME | exact HMN]. }
                   split; [unfold ps_gptp; rewrite K3, K4; exact HGP|].
                   split; [rewrite K2; exact R2|].
                   split; [exact HRL|].
                   split; [rewrite (psc_held_none _ Hnone); lia|].
                   unfold ps_Qres. rewrite Hnone.
                   split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact HLED|].
                   split; [exact HPJ | exact (PS_Gen.ps_rpos_nil (L := B_prog_listing) (PA := PSB_PAImg) D)].
Qed.

(* ---- AFTER THE CALL: small facts ---- *)
Lemma psc_frame : PS_FRAME = 144.
Proof. vm_compute. reflexivity. Qed.
(* parse_string's stack budget covers fuzz_malloc's below its own frame (computed at prh_img_B) *)
Lemma psc_stk_ps : STK_fuzz_malloc + PS_FRAME <= STK_parse_string /\ 0 <= STK_fuzz_malloc.
Proof.
assert (H1 : (STK_fuzz_malloc + PS_FRAME <=? STK_parse_string) = true) by (vm_compute; reflexivity).
assert (H2 : (0 <=? STK_fuzz_malloc) = true) by (vm_compute; reflexivity).
apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

(* fuzz_malloc's post body at this call (the kit's tfuzz_malloc_specX, lib/A/PRH_FnAlloc.v, VERBATIM at the entry's
   allocator state, n = Q + 1): the predicate the callee text's m-form post (fQmn memc) carries, with the memnorm keep
   beside it. The third conjunct is the call's hull use (at most its one event HMal (n + cf_head)). POST-IMPLICATION: a
   NULL transfers every position by E = [], a block by its own event HMal (n + cf_head); the sixth conjunct is the
   batch's OUTCOME clause (a granted request at a consumer position is not refused), from which the refused arm reads
   its exclusion (PS_Gen.ps_excl_of_malloc) *)
Definition psc_malloc_KC (D : ps_in) (Q : nat) :
  alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' md' => exists res, getr regs' 10 = w64 res /\ room_live_cf S' /\
    PresetHullBudget.hull_used (pi_S D) S' [PresetReqAt.HMal ((Z.of_nat Q + 1) + cf_head)] /\
    (res = 0 -> forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
       (i : nat) (H0 : list Z) (hist : list YG00.chunk),
       PresetRoomPos.iface_room_pos sm x os i H0 hist (pi_S D) -> PRH_Base.prh_run_at sm x os i [] ->
       exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (@nil PresetReqAt.hev))%nat H0 hist' S') /\
    (res <> 0 -> forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
       (i : nat) (H0 : list Z) (hist : list YG00.chunk),
       PresetRoomPos.iface_room_pos sm x os i H0 hist (pi_S D) ->
       PRH_Base.prh_run_at sm x os i [PresetReqAt.HMal ((Z.of_nat Q + 1) + cf_head)] ->
       exists hist', PresetRoomPos.iface_room_pos sm x os (i + length [PresetReqAt.HMal ((Z.of_nat Q + 1) + cf_head)])%nat
         H0 hist' S') /\
    (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
       (i : nat) (H0 : list Z) (hist : list YG00.chunk),
       PresetRoomPos.iface_room_pos sm x os i H0 hist (pi_S D) ->
       PRH_Base.prh_run_at sm x os i [PresetReqAt.HMal ((Z.of_nat Q + 1) + cf_head)] ->
       PRH_Base.prh_cons_from sm x os i (length [PresetReqAt.HMal ((Z.of_nat Q + 1) + cf_head)]) ->
       pi_cnt D <> pi_fail D ->
       res <> 0 /\
       exists hist', PresetRoomPos.iface_room_pos sm x os (i + length [PresetReqAt.HMal ((Z.of_nat Q + 1) + cf_head)])%nat
         H0 hist' S') /\
    prh_alloc_post (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg) B (Z.of_nat Q + 1)
      (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_Lam D) (pi_peak D) (pi_cnt D) (pi_fail D) (pi_ran D) (pi_most D)
      (pi_own D) res ly' S' Hp' W' mem'.

(* THE ONE fuzz_malloc CALL STEP: the kit's tfuzz_malloc_specX (the cut's PRH_FnAlloc blob 4d8aeba047e5) at the call
   state (S = the entry's, no allocation before), n = Q + 1, with its m-form post fpostm (the post body at fQmn memc: the
   memnorm keep from the call memory). Its premises are the call state's, fpre's five conjuncts among them (the return
   address below the ceiling is the caller's to give, from the jal's return pc; frm_zero is the entry's, the same fx);
   the two live counts are ps_pre's peaks at the first state (PS_Gen.ps_counts_entry), the hull budget ps_pre's at its
   first event (PS_Gen.ps_hull_mal) *)
Lemma psc_malloc_text : forall CTX CW (D : ps_in) regsc memc mdc ch Q,
  ps_pre CTX CW D -> PjGrammar.scan (ps_x D) = Some Q ->
  afn_pre_x segs B ARx STK_fuzz_malloc (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) regsc memc mdc ch ->
  arodata_okP segs (@pa_relro_lo _ B_prog_listing PSB_PAImg) (@pa_relro_hi _ B_prog_listing PSB_PAImg) B
    (aview segs (w_H (pi_W D)) memc) ->
  spZ regsc + 64 <= ly_stk_hi (pi_ly D) ->
  raZ regsc < YM05.alloc_ceiling ->
  getr regsc 10 = w64 (Z.of_nat Q + 1) ->
  LEDGER (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) memc (pi_Lam D) (pi_peak D) (pi_cnt D) (pi_fail D) (pi_ran D)
    (pi_most D) (pi_own D) ->
  SRr segs (pi_W D) (cfg_at segs (@pa_sigma _ B_prog_listing PSB_PAImg AS_fuzz_malloc) regsc memc mdc)
    (fpostm B ARx SK STK_fuzz_malloc [] regsc (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) memc mdc (psc_malloc_KC D Q)).
Proof.
intros CTX CW D regsc memc mdc ch Q HPRE HQ HAFN HROD Htop Hra H10 HLED.
pose proof HPRE as ((_ & _ & _ & _ & HFRM) & HCL & _ & _ & _ & _ & HRL & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & HLIVE).
destruct (ps_counts_entry (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg) B ARx CTX CW D Q HPRE HQ)
  as [HSEC H24].
(* the request bound and the call's room: the text's per-event live premise at its event 0 (the kit cut 7cdbb61b5fa0,
   PRH_FnReader f1ae32e3b2cd :566-576; PS_Gen.ps_room_entry) *)
destruct (ps_room_entry (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg) B ARx CTX CW D Q HPRE HQ)
  as [Hmax Hbb].
unfold LIVE_parse_string in Hmax. unfold psc_malloc_KC.
apply (HMALLOC (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) regsc memc mdc ch (Z.of_nat Q + 1)
  (pi_Lam D) (pi_peak D) (pi_cnt D) (pi_fail D) (pi_ran D) (pi_most D) (pi_own D)).
- exact (conj HAFN (conj HROD (conj Htop (conj Hra HFRM)))).
- exact HRL.
- eapply prh_univ_closure_malloc; [exact HCL|]. vm_compute. intros Hn. discriminate Hn.
- exact HSEC.
- exact H24.
- exact (ps_hull_mal (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg) B ARx CTX CW D Q HPRE HQ).
- exact H10.
- lia.
- lia.
- exact HLED.
- (* the batch's per-call room, guarded by the call's success flag (PRH_FnAlloc 4d8aeba047e5 :277-283) *)
  intros _. lia.
Qed.
Lemma psc_preserved_reg : forall regs regs' (r : bv 5), aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) ->
  getr regs' r = getr regs r.
Proof. intros regs regs' r HP Hr. pose proof (HP (bv_unsigned r) Hr) as H. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
Lemma psc_preserved_trans : forall r1 r2 r3, aregs_preserved r1 r2 -> aregs_preserved r2 r3 -> aregs_preserved r1 r3.
Proof. intros r1 r2 r3 H12 H23 r Hr. rewrite (H23 r Hr). exact (H12 r Hr). Qed.
Ltac psc_cs := lazymatch goal with |- acallee_saved ?t =>
  let v := eval vm_compute in t in change t with v; unfold acallee_saved; lia end.
Ltac psc_pres HP := apply (psc_preserved_reg _ _ _ HP); psc_cs.

(* a value read over a view that agrees on its bytes *)
Lemma psc_val_mem_kept : forall (W W2 : world segs) m m2 a n v,
  (forall k, (k < n)%nat -> aview segs (w_H W2) m2 (a + Z.of_nat k) = aview segs (w_H W) m (a + Z.of_nat k)) ->
  val_mem segs (rdW W m) a n v -> val_mem segs (rdW W2 m2) a n v.
Proof.
intros W W2 m m2 a n v HA H k Hk.
rewrite (mbyte_of_aview segs (w_H W) (w_H W2) m m2 (a + Z.of_nat k) (HA k Hk)). exact (H k Hk).
Qed.
(* a shadow byte 0 as a one-byte value *)
Lemma psc_val1_zero : forall H (m : word -> option byte) a, aview segs H m a = Some 0 -> val_mem segs (mrestrict H m) a 1 0.
Proof.
intros H m a Hz k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r.
destruct (aview_byte segs H m a 0 Hz) as (b & Hb & Hv & _). rewrite Hb. f_equal.
apply bv_eq. rewrite Z_to_bv_unsigned. rewrite <- Hv. vm_compute. reflexivity.
Qed.
(* an 8-byte value is read modulo 2 ^ 64 *)
Lemma psc_val_mem_mod : forall m a v v', v mod 2 ^ 64 = v' mod 2 ^ 64 -> val_mem segs m a 8 v -> val_mem segs m a 8 v'.
Proof.
intros m a v v' Hv H k Hk. rewrite (H k Hk). do 2 f_equal.
first [unfold YO0f.le_byte | unfold le_byte]. replace (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) by reflexivity.
rewrite Hv. reflexivity.
Qed.
(* the shadow of a low address, and the hull of a low range, are below 2 ^ 46 (FuzzStrdupB.v's sd_shadow_low /
   sd_hull_low) *)
Lemma psc_shadow_low : forall x, 0 <= x < 2 ^ 47 -> 0 <= shadow_of_addr SHADOW_OFF x < 2 ^ 46.
Proof.
intros x Hx. unfold shadow_of_addr, SHADOW_OFF.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.
Lemma psc_hull_low : forall x n s, 0 <= x -> 0 < n -> x + n <= 2 ^ 47 ->
  shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> 0 <= s < 2 ^ 46.
Proof.
intros x n s H0 Hn Hx Hs. unfold shadow_addr in Hs.
pose proof (Z.div_pos x 8 H0 ltac:(lia)) as P1.
pose proof (Z.div_pos (SHADOW_OFF + x / 8) 8 ltac:(unfold SHADOW_OFF; lia) ltac:(lia)) as P2.
assert (P3 : (x + n - 1) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
assert (P4 : (SHADOW_OFF + (x + n - 1) / 8) / 8 <= 2 ^ 42) by (apply Z.div_le_upper_bound; unfold SHADOW_OFF; lia).
lia.
Qed.

(* ---- the reads of the stretch below alloc_ceiling survive a change above it (the frame stores) ---- *)
Lemma psc_src_low : forall (W : world segs) m m' t tb, src_rd W m t tb ->
  (forall a, 0 <= a < YM05.alloc_ceiling -> aview segs (w_H W) m' a = aview segs (w_H W) m a) ->
  src_rd W m' t tb.
Proof.
intros W m m' t tb (HB & H4096 & Hceil & Hamr & HRA & HHU) HL. pose proof asan_consts as (C1 & _).
split; [|split; [exact H4096|]; split; [exact Hceil|]; split; [exact Hamr|]; split].
- apply (psb_src_garr8 W W m m' t tb); [|exact HB]. intros j Hj. apply HL. lia.
- eapply range_addressable_agree; [|exact HRA]. intros y Hy. apply HL. pose proof (psc_shadow_low y ltac:(lia)). lia.
- intros Hn s Hs. pose proof (psc_hull_low t _ s ltac:(lia) Hn ltac:(lia) Hs). rewrite HL by lia. exact (HHU Hn s Hs).
Qed.
Lemma psc_vis_low : forall (W : world segs) m m' a n, prhReader_vis W m a n -> 0 <= a -> 0 <= n -> a + n <= 2 ^ 47 ->
  (forall y, 0 <= y < YM05.alloc_ceiling -> aview segs (w_H W) m' y = aview segs (w_H W) m y) ->
  prhReader_vis W m' a n.
Proof.
intros W m m' a n (HRA & HHU) Ha Hn Han HL. pose proof asan_consts as (C1 & _). split.
- eapply range_addressable_agree; [|exact HRA]. intros y Hy. apply HL. pose proof (psc_shadow_low y ltac:(lia)). lia.
- intros Hn0 s Hs. pose proof (psc_hull_low a n s Ha Hn0 Han Hs). rewrite HL by lia. exact (HHU Hn0 s Hs).
Qed.
Lemma psc_ledger_low : forall ly S Hp W m m' memX mdX Lam peak cnt fail ran most own,
  ARx ly S Hp W memX mdX -> LEDGER ly S Hp W m Lam peak cnt fail ran most own ->
  (forall a, 0 <= a < YM05.alloc_ceiling -> aview segs (w_H W) m' a = aview segs (w_H W) m a) ->
  LEDGER ly S Hp W m' Lam peak cnt fail ran most own.
Proof.
intros ly S Hp W m m' memX mdX Lam peak cnt fail ran most own HAR (HG & HND & HF & HP) HL.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof ASAN_CEIL_range as (_ & Hc16). unfold ASAN_CEIL in Hc16.
assert (Hst : forall p (n : nat) v, (forall k, (k < n)%nat -> Exists (in_zr (p + Z.of_nat k)) PST) ->
  val_mem segs (rdW W m) p n v -> val_mem segs (rdW W m') p n v).
{ intros p n v Hin Hv. apply (psc_val_mem_kept W W m m'); [|exact Hv]. intros k Hk. apply HL.
  destruct (PST_ok _ (Hin k Hk)) as [Hi _]. pose proof (@pa_segs_low _ _ PSB_PAImg _ Hi). lia. }
split; [|split; [exact HND|]; split; [|exact HP]].
- destruct HG as (G1 & G2 & G3 & G4 & G5 & (G6 & G6r) & (G7 & G7r) & G8).
  split; [apply Hst; [intros k Hk; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | exact G1]|].
  split; [apply Hst; [intros k Hk; do 1 apply Exists_cons_tl; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | exact G2]|].
  split; [apply Hst; [intros k Hk; do 2 apply Exists_cons_tl; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | exact G3]|].
  split; [apply Hst; [intros k Hk; do 3 apply Exists_cons_tl; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | exact G4]|].
  split; [apply Hst; [intros k Hk; do 4 apply Exists_cons_tl; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | exact G5]|].
  (* the #102 cells g_most / g_own_ran_out (prh_glob's prh_most / prh_own, the sixth and seventh prh_pst cells) *)
  split; [split; [apply Hst; [intros k Hk; do 5 apply Exists_cons_tl; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | exact G6] | exact G6r]|].
  split; [split; [apply Hst; [intros k Hk; do 6 apply Exists_cons_tl; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | exact G7] | exact G7r]|].
  exact G8.
- refine (Forall_impl _ _ HF). intros [a k] (Hk0 & Hab & Hhp & Ha16 & Hv). cbn [fst snd] in *.
  split; [exact Hk0|]. split; [exact Hab|]. split; [exact Hhp|]. split; [exact Ha16|].
  destruct (alx_blocks segs B ARx LAWS ly S Hp W memX mdX _ _ HAR Hab) as (Hb16 & Hb4096 & Hbc & _).
  pose proof cf_head_nonneg as Hh0. pose proof (req_size_pos (k + cf_head)) as RS. specialize (RS ltac:(lia)).
  destruct RS as [R1 _].
  assert (Hlt : a - cf_head + 8 <= YM05.alloc_ceiling).
  { clear - Hb16 Hbc R1 Hc16. Z.div_mod_to_equations. lia. }
  apply (psc_val_mem_kept W W m m'); [|exact Hv]. intros j Hj. cbn in Hj. apply HL. clear - Hlt Hj Hb4096. lia.
Qed.
(* pj_in_okR over a view that agrees on q's struct (and keeps it present), with the text's bytes there *)
Lemma psc_pj_kept : forall (W W2 : world segs) m m2 q text len p d tb,
  pj_in_okR segs (rdW W m) q text len p d tb ->
  (forall a, q <= a < q + 24 -> aview segs (w_H W2) m2 a = aview segs (w_H W) m a) ->
  (forall a, q <= a < q + 24 -> apresent (w_H W2) m2 a) ->
  garr8 segs (rdW W2 m2) text tb ->
  pj_in_okR segs (rdW W2 m2) q text len p d tb.
Proof.
intros W W2 m m2 q text len p d tb (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12) Hq Hqp Ht.
split; [apply (psc_val_mem_kept W W2 m m2); [intros k Hk; apply Hq; cbn in Hk; lia | exact H1]|].
split; [apply (psc_val_mem_kept W W2 m m2); [intros k Hk; apply Hq; cbn in Hk; lia | exact H2]|].
split; [apply (psc_val_mem_kept W W2 m m2); [intros k Hk; apply Hq; cbn in Hk; lia | exact H3]|].
split; [intros y Hy; apply apresent_writable; apply Hqp; exact Hy|].
split; [exact H5|]. split; [exact H6|]. split; [exact H7|]. split; [exact H8|]. split; [exact H9|].
split; [exact Ht|].
split; [exact H11 | exact H12].
Qed.
(* the read-only view over a view that agrees on the image bytes the journal's image clause keeps *)
Lemma psc_rod_kept : forall (W W2 : world segs) m m2,
  arodata_okP segs (@pa_relro_lo _ B_prog_listing PSB_PAImg) (@pa_relro_hi _ B_prog_listing PSB_PAImg) B
    (aview segs (w_H W) m) ->
  (forall a, in_img segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     ~ Exists (in_zr a) PST -> aview segs (w_H W2) m2 a = aview segs (w_H W) m a) ->
  arodata_okP segs (@pa_relro_lo _ B_prog_listing PSB_PAImg) (@pa_relro_hi _ B_prog_listing PSB_PAImg) B
    (aview segs (w_H W2) m2).
Proof.
intros W W2 m m2 H HK a Hro Hn He. rewrite HK; [exact (H a Hro Hn He) | exact (psbs_ro_img a Hro) | exact Hn | exact He |].
exact (fun Hx => psb_pst_not_ro a Hx Hro).
Qed.
(* the saved registers over a view that agrees on the frame's save slots *)
Lemma psc_saved_kept : forall (D : ps_in) (W W2 : world segs) m m2, ps_saved D W m ->
  (forall a, PS_SP D + 40 <= a < PS_SP D + 144 -> aview segs (w_H W2) m2 a = aview segs (w_H W) m a) ->
  ps_saved D W2 m2.
Proof.
intros D W W2 m m2 HSV HK. unfold ps_saved in *. cbv zeta in *.
repeat match goal with H : _ /\ _ |- _ => destruct H end.
repeat split; (apply (psc_val_mem_kept W W2 m m2); [intros k Hk; apply HK; cbn in Hk; lia | assumption]).
Qed.

(* ---- the symbolic state at 228 (after the call) from the concrete facts there ---- *)
Definition PSA_E (regs : bvmap 5 word) (e : Z) : env := EB (Ereg regs [Z_to_bv 64 e]).
Lemma psa_ew_reg : forall regs e n (r : bv 5), Z.of_nat n = bv_unsigned r -> (n < 32)%nat ->
  ew (PSA_E regs e) n = getr regs r.
Proof.
  intros regs e n r Hn H32. unfold PSA_E. rewrite Eimg_low by (unfold A_TEXT; lia).
  exact (ew_Ereg_nat regs _ n r Hn).
Qed.
Lemma psa_ew_end : forall regs e, ew (PSA_E regs e) 32 = Z_to_bv 64 e.
Proof.
  intros regs e. unfold PSA_E. rewrite Eimg_low by (unfold A_TEXT; lia).
  replace 32%nat with (32 + 0)%nat by lia. rewrite ew_Ereg_extra. reflexivity.
Qed.
Lemma psa_entry : forall (W : world segs) regs mem e s8 q sp,
  bv_unsigned (getr regs 24) = s8 -> aview segs (w_H W) mem s8 = Some 0 ->
  bv_unsigned (getr regs 9) = q + 8 -> val_mem segs (rdW W mem) (q + 8) 8 e -> 0 <= e < 2 ^ 64 ->
  bv_unsigned (getr regs 2) = sp -> sp mod 16 = 0 -> 2 ^ 46 <= sp <= 2 ^ 47 ->
  (forall o, 8 <= o < 32 -> apresent (w_H W) mem (sp + o)) ->
  0 <= s8 -> s8 + 1 <= sp + 8 -> sp + 32 <= q + 8 -> q + 16 <= 2 ^ 64 ->
  st_ok_pi segs VAL (PSA_E regs e) ss_psa
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (PSB_OFF + PSC_RET))) mem (seg_rom segs)))
  /\ sh_ok segs PSC_Bx [] (PSA_E regs e) (rdW W mem).
Proof.
intros W regs mem e s8 q sp U24 Hz U9 He Herng U2 Hal Hsp Hpres H0 Hd1 Hd2 Hq64.
rewrite restrict_mkst_fx.
set (E := PSA_E regs e).
assert (V24 : bv_unsigned (ew E 24) = s8) by (subst E; rewrite (psa_ew_reg regs e 24 24%bv eq_refl ltac:(lia)); exact U24).
assert (V9 : bv_unsigned (ew E 9) = q + 8) by (subst E; rewrite (psa_ew_reg regs e 9 9%bv eq_refl ltac:(lia)); exact U9).
assert (V2 : bv_unsigned (ew E 2) = sp) by (subst E; rewrite (psa_ew_reg regs e 2 2%bv eq_refl ltac:(lia)); exact U2).
assert (E32 : ew E 32 = Z_to_bv 64 e) by (subst E; apply psa_ew_end).
split.
- unfold ss_psa. apply pa_entry_st_ok_full.
  + subst E. unfold PSA_E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold psa_regions. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]];
      unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite V24. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ s8 0 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (psc_val1_zero (w_H W) mem s8 Hz).
    * rewrite V9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ (q + 8) 0 8 (SOff 32 0) e).
      -- cbn [sv_denot]. rewrite E32, Z.add_0_r. rewrite unsigned_lit_small by lia. reflexivity.
      -- cbn. lia.
      -- cbn. lia.
      -- rewrite Z.add_0_r. exact He.
    * rewrite V2. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply apresent_writable; apply Hpres; lia | apply Forall_nil].
  + unfold psa_regions. cbn [pairwise_disjoint all_disjoint].
    unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite V24, V9, V2.
    repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [psa_facts f_atoms atoms_ok]. split; [|exact I].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite V2. change (2 ^ 4) with 16. lia.
- unfold sh_ok. apply Forall_nil.
Qed.

(* a register the post-call run leaves alone holds the atom the state names for it *)
Lemma psa_reg_kept : forall (H : word -> bool) ss ms regs e (r rr : bv 5) n,
  st_ok_pi segs VAL (PSA_E regs e) ss (restrict H ms) ->
  sr_get (ss_regs ss) r = SOff n 0 -> Z.of_nat n = bv_unsigned rr -> (n < 32)%nat ->
  getr (ms_regs ms) r = getr regs rr.
Proof.
intros H ss ms regs e r rr n HS Hr Hn H32.
rewrite (st_ok_pi_restrict_reg H _ ss ms r HS), Hr.
rewrite (denot_lit_U _ (SOff n 0)), U_SOff, Z.add_0_r.
rewrite (psa_ew_reg regs e n rr Hn H32). unfold zcanon, M64.
rewrite Z.mod_small by (pose proof (bv_unsigned_in_range 64 (getr regs rr)) as Hb; unfold bv_modulus in Hb; lia).
apply Z_to_bv_bv_unsigned.
Qed.
Ltac psa_kr HS := eapply (psa_reg_kept _ _ _ _ _ _ _ _ HS); [vm_compute; reflexivity | reflexivity | lia].
(* a register the post-call run sets to a constant (the decode constants of offsets 252 .. 312) *)
Ltac psa_lit HS := lazymatch goal with |- getr _ ?r = _ =>
  rewrite (st_ok_pi_restrict_reg _ _ _ _ r HS);
  lazymatch goal with |- sv_denot ?E (sr_get ?sr ?r') = _ =>
    let v := eval vm_compute in (sr_get sr r') in change (sr_get sr r') with v end;
  cbn [sv_denot]; unfold w64; apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity end.
(* the post-call run's write premise: two read-only regions, the surrogate slots in parse_string's own frame *)
Ltac psa_awr D U2 :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0 ?bc ?ly' ?own' =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0 bc ly' own') end;
  apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|];
  lazymatch goal with |- awr_ok _ _ _ ?sp0' _ _ _ _ _ =>
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (PS_SP D - sp0')) end;
  [ reflexivity | rewrite U2; lia | cbn [YP09.r_wlo]; unfold PS_Gen.PS_SP, PS_WSP, PS_WSTK in *; lia
  | cbn [YP09.r_whi]; unfold PS_Gen.PS_SP, PS_WSP, PS_WSTK in *; lia | apply awr_ok_nil ].

(* the success arm's block is new: it was not in the call state's block list (FuzzStrdupB.v's sd_newblk) *)
Lemma psc_newblk : forall ly S ly' S' Hp' W' m' md' (x : Z * Z), ARx ly' S' Hp' W' m' md' -> 0 <= snd x ->
  ablocks B ly' S' = ablocks B ly S ++ [x] -> ~ In x (ablocks B ly S).
Proof.
intros ly S ly' S' Hp' W' m' md' [p n] HAR Hn E Hin. cbn [snd] in Hn.
assert (Hin' : In (p, n) (ablocks B ly' S')) by (rewrite E; apply in_or_app; right; left; reflexivity).
destruct (alx_blocks segs B ARx LAWS ly' S' Hp' W' m' md' p n HAR Hin') as (_ & _ & _ & _ & _ & Hpw).
rewrite E in Hpw. apply in_split in Hin as (l1 & l2 & El). rewrite El in Hpw.
pose proof (pairwise_In2 zdisjoint _ (p, req_size n) (p, req_size n)
  (map (fun b : Z * Z => (fst b, req_size (snd b))) l1) (map (fun b : Z * Z => (fst b, req_size (snd b))) l2) [] Hpw
  ltac:(rewrite <- app_assoc, !map_app; reflexivity)) as Dj.
unfold zdisjoint in Dj. cbn [fst snd] in Dj. pose proof (req_size_pos n Hn). lia.
Qed.
(* ... and its base is no old block's base *)
Lemma psc_newbase : forall ly S ly' S' Hp' W' m' md' p n b m, ARx ly' S' Hp' W' m' md' -> 0 <= m -> 0 <= n ->
  ablocks B ly' S' = ablocks B ly S ++ [(b, m)] -> In (p, n) (ablocks B ly S) -> p <> b.
Proof.
intros ly S ly' S' Hp' W' m' md' p n b m HAR Hm Hn E Hin Epb. subst p.
destruct (Z.eq_dec n m) as [<-|Hnm].
- exact (psc_newblk ly S ly' S' Hp' W' m' md' (b, n) HAR Hm E Hin).
- assert (H1 : In (b, n) (ablocks B ly' S')) by (rewrite E; apply in_or_app; left; exact Hin).
  assert (H2 : In (b, m) (ablocks B ly' S')) by (rewrite E; apply in_or_app; right; left; reflexivity).
  assert (Hne : (b, n) <> (b, m)) by (intros Ee; injection Ee as Ee; exact (Hnm Ee)).
  pose proof (sep_blocks_x segs B ARx LAWS ly' S' Hp' W' m' md' b n b m HAR H1 H2 Hne) as Dj.
  unfold zdisjoint in Dj. cbn [fst snd] in Dj. pose proof (req_size_pos n Hn). pose proof (req_size_pos m Hm). lia.
Qed.
(* every hidden head of a ledger state is a live block's base *)
Lemma psc_hp_live : forall ly S Hp W m Lam peak cnt fail ran most own, LEDGER ly S Hp W m Lam peak cnt fail ran most own ->
  forall h, In h Hp -> exists k, 0 <= k /\ In (h, k) (ablocks B ly S).
Proof.
intros ly S Hp W m Lam peak cnt fail ran most own (_ & _ & HF & HP) h Hh.
apply (Permutation_in _ HP) in Hh. apply in_map_iff in Hh as ([a k] & Eh & Hin). cbn [fst] in Eh.
pose proof (proj1 (Forall_forall _ _) HF _ Hin) as (Hk0 & Hab & _). cbn [fst snd] in *.
exists (k + cf_head). split; [pose proof cf_head_nonneg; lia|]. rewrite <- Eh. exact Hab.
Qed.
(* the walk's charge is never negative *)
Lemma psc_held_nonneg : forall x, 0 <= PRH_Charge.prh_held (PRH_Charge.prhPs_gtrace x).
Proof.
intros x. pose proof cf_head_nonneg as Hh.
unfold PRH_Charge.prh_held, PRH_Charge.prhPs_gtrace, PjGrammar.jr_string.
destruct (PjGrammar.scan x) as [Q|].
- destruct (PjGrammar.decode x) as [sr|];
    cbn [PjGrammar.jbind PjGrammar.jalloc PjGrammar.take PjGrammar.jret PjGrammar.jfree PjGrammar.jrefuse
         fst snd app PjGrammar.held PjGrammar.held_ev PjGrammar.calls PjGrammar.is_call]; lia.
- cbn [PjGrammar.jrefuse fst snd PjGrammar.held PjGrammar.calls]. lia.
Qed.

(* THE END OF THE POST-CALL STRETCH: the carried facts across the run from 228 (it writes only the surrogate slots);
   P at the end memory is the last run's (the runner twin's) *)
Lemma psc_final : forall CTX CW (D : ps_in) ly2 S2 Hp2 W2 mem2 md2 memF mdF k k',
  ps_pre CTX CW D ->
  AJ (PS_WSTK D) (PS_WSP D) [(pi_q D, pi_q D + 8)] (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) []
    ly2 S2 Hp2 W2 memF mdF k ->
  AJ (PS_WSTK D) (PS_WSP D) [(pi_q D, pi_q D + 8)] (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) []
    ly2 S2 Hp2 W2 mem2 md2 k' ->
  KEPT STK_parse_string (spZ (pi_regs D)) [(pi_q D, pi_q D + 8)] [] (pi_ly D) (pi_S D) (pi_W D) (pi_mem D) (pi_md D)
    ly2 S2 W2 mem2 md2 ->
  (forall x0 : word, ~ (PS_SP D + 8 <= bv_unsigned x0 < PS_SP D + 32) ->
     mrestrict (w_H W2) memF x0 = mrestrict (w_H W2) mem2 x0) ->
  same_but_materialized md2 mdF ->
  ps_saved D W2 mem2 -> src_rd W2 mem2 (pi_text D) (pi_tb D) ->
  prhReader_home B ly2 S2 Hp2 (pi_Lam D) (pi_text D) (pi_len D) ->
  P memF ->
  ps_carryP D ly2 S2 Hp2 W2 memF mdF k [] /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (PS_SP D + 8 <= a < PS_SP D + 32) ->
     aview segs (w_H W2) memF a = aview segs (w_H W2) mem2 a).
Proof.
intros CTX CW D ly2 S2 Hp2 W2 mem2 md2 memF mdF k k' HPRE HJF HJ2 K_ep HFW Hsame HSV2 HSRC2 HHOME2 HMNF.
pose proof HPRE as (HFP & _). pose proof HFP as (HAFN & _). pose proof HAFN as (HAR0 & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil0 & Hslo & Hshi & H47 & _).
pose proof (ajx_ar HJ2) as HAR2. pose proof (ajx_ly HJ2) as Hly2.
pose proof Hly2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo2 & Ehi2 & _).
pose proof psc_frame as HFR. pose proof psc_stk_ps as HSTK. pose proof asan_consts as (C1 & _).
assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (PS_SP D + 8 <= a < PS_SP D + 32) ->
  aview segs (w_H W2) memF a = aview segs (w_H W2) mem2 a).
{ intros a Ha Hn. apply aview_eq_of. apply HFW. rewrite unsigned_lit_small by lia. exact Hn. }
split; [|exact KF].
split; [exact HJF|].
split.
{ eapply (cj_kept_trans (SK := SK) segs B PST ARx LAWS); [exact K_ep | | exact HAR0 | exact HAR2 | | | |].
  - eapply (cj_kept_exec (SK := SK) segs B PST ARx LAWS (@pa_segs_low _ _ PSB_PAImg) STK_parse_string (spZ (pi_regs D))
      [(pi_q D, pi_q D + 8)] [] ly2 S2 Hp2 W2 mem2 md2 memF mdF (fun a => PS_SP D + 8 <= a < PS_SP D + 32)).
    + exact HAR2.
    + rewrite Elo2. lia.
    + rewrite Elo2. lia.
    + rewrite Ehi2. lia.
    + exact HFW.
    + intros a Ha. left. unfold PS_Gen.PS_SP in Ha. rewrite HFR in Ha. lia.
    + exact Hsame.
  - apply Z.le_refl.
  - apply Z.le_refl.
  - intros a Ha. exfalso. exact (inFP_nil a Ha).
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
split.
{ apply (psc_saved_kept D W2 W2 mem2 memF HSV2). intros a Ha. apply KF; unfold PS_Gen.PS_SP in *; rewrite ?HFR in *; lia. }
split.
{ apply (psc_src_low W2 mem2 memF _ _ HSRC2). intros a Ha. apply KF; unfold PS_Gen.PS_SP; rewrite ?HFR; lia. }
split; [exact HHOME2 | exact HMNF].
Qed.

(* THE POST-CALL STRETCH: from the return point 228 of `jal fuzz_malloc`, the three arms of prh_alloc_post: the two
   refusing arms (a0 = 0) by `beqz a0` to PSB_RET0; the success arm through the q + 8 shadow re-check, the end
   reload, `bgeu s4, a0` (not taken), the constants block and the three surrogate words to PSB_DEC. P at the memory
   after the call (HMN2: the callee text's keep through PCALL) is the runs' invariant premise *)
Lemma psc_post_call : forall CTX CW (D : ps_in) regs mem mdc x regsc W2 ly2 S2 Hp2 regs2 mem2 md2 k1 res,
  psb_seg_ret0P B ARx SK CTX CW P -> psb_seg_decP B ARx SK CTX CW P -> ps_pre CTX CW D ->
  psb_at_scanP B ARx SK P D (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) regs mem mdc x ->
  nth_error (pi_tb D) (Z.to_nat (x - pi_text D)) = Some 34 ->
  aregs_preserved regs regsc ->
  AJ (PS_WSTK D) (PS_WSP D) [(pi_q D, pi_q D + 8)] (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) []
    ly2 S2 Hp2 W2 mem2 md2 (0 + k1) ->
  AJ STK_fuzz_malloc (PS_WSP D + (- pi_e D - PS_FRAME)) [] (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) mem mdc []
    ly2 S2 Hp2 W2 mem2 md2 k1 ->
  aregs_preserved regsc regs2 ->
  getr regs2 10 = w64 res -> room_live_cf S2 ->
  (res = 0 -> ps_rpos D [] S2) -> (res <> 0 -> ps_rpos D [PresetReqAt.HMal (x - pi_p D + cf_head)] S2) ->
  (res = 0 -> pi_cnt D <> pi_fail D -> ps_excl D) ->
  prh_alloc_post (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg) B (x - pi_p D)
    (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_Lam D) (pi_peak D) (pi_cnt D) (pi_fail D) (pi_ran D) (pi_most D) (pi_own D)
    res ly2 S2 Hp2 W2 mem2 ->
  P mem2 ->
  SRr segs W2 (mkCfg (YK11.mkst regs2 (Z_to_bv 64 (BASE + (PSB_OFF + PSC_RET))) mem2 (YK11.seg_rom segs)) md2)
    (ps_finP CW D).
Proof.
intros CTX CW D regs mem mdc x regsc W2 ly2 S2 Hp2 regs2 mem2 md2 k1 res HRET0 HDEC HPRE HAT Hbyte HPsc HJ2 HJc HP2
  Hres HRL2 HRP0 HRPM HEX HAP HMN2.
pose proof HAT as (HC & HSH & HGP & _ & _ & _ & _ & HLED & HPJ & HROD & R2 & R10 & R11 & R12 & R8 & R9 & R20 & Hx & Heq).
pose proof HC as (HJ & HKEPT & HSAVED & HSRC & HHOME & _).
pose proof HSH as (R23 & R22 & R24).
pose proof HPJ as (_ & HEND & _ & _ & Hq8 & Htpos & Htlen & Hple & Hlen & _).
pose proof HSRC as (HBY & Ht4096 & Htceil & Htamr & HRA & _).
pose proof HPRE as (HFP & HCL & _ & _ & _ & HGAP & HRL & HRP & _ & _ & HPJ0 & _ & _ & HWIN & Hqlo & Hqhi & HRAq & _ & _ &
  _ & HCNT & HLIVE).
pose proof HFP as (HAFN & _ & Htop64).
pose proof HAFN as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & _ & HQT0).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil0 & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HWIN as (He0 & He16 & Hetop & Hepres).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof psc_frame as HFR.
assert (Rsp : 2 ^ 46 <= spZ (pi_regs D) <= 2 ^ 47) by lia.
assert (Hx47 : x < 2 ^ 47) by lia.
(* the registers after the call: the callee-saved ones are the scan's *)
pose proof (psc_preserved_trans _ _ _ HPsc HP2) as HP.
assert (P2 : getr regs2 2 = getr regs 2) by psc_pres HP.
assert (P3 : getr regs2 3 = getr regs 3) by psc_pres HP.
assert (P4 : getr regs2 4 = getr regs 4) by psc_pres HP.
assert (P8 : getr regs2 8 = getr regs 8) by psc_pres HP.
assert (P9 : getr regs2 9 = getr regs 9) by psc_pres HP.
assert (P20 : getr regs2 20 = getr regs 20) by psc_pres HP.
assert (P22 : getr regs2 22 = getr regs 22) by psc_pres HP.
assert (P23 : getr regs2 23 = getr regs 23) by psc_pres HP.
assert (P24 : getr regs2 24 = getr regs 24) by psc_pres HP.
(* the callee's journal (from the call state) and the caller's (from entry) at the post state *)
pose proof (ajx_ar HJc) as HAR2. pose proof (ajx_ly HJc) as Hlyc. pose proof (ajx_hi HJc) as F1c.
pose proof (ajx_blk HJc) as F2c. pose proof (ajx_img HJc) as F3c. pose proof (ajx_frm HJc) as F4c.
pose proof (ajx_gone HJc) as Fgc. pose proof (ajx_extra HJc) as F5c.
pose proof (ajx_ly HJ2) as Hly2. pose proof (ajx_pres HJ2) as Hpres2.
pose proof Hly2 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop2 & Elo2 & Ehi2 & _).
(* the shadow byte of q + 8, still 0: q's struct is on the real stack (ARx's stack-shadow law at the post state) *)
assert (HZ8 : aview segs (w_H W2) mem2 (SHADOW_OFF + (pi_q D + 8) / 8) = Some 0).
{ apply (alx_zshadow_byte segs B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 (pi_q D + 8) HAR2). rewrite Elo2, Ehi2. lia. }
(* the end word at q + 8, kept by the callee's stack clause (q + 8 is above the callee's window) *)
assert (HEND2 : val_mem segs (rdW W2 mem2) (pi_q D + 8) 8 (pi_text D + pi_len D)).
{ apply (psc_val_mem_kept (pi_W D) W2 mem mem2); [|exact HEND]. intros k Hk. cbn in Hk.
  apply F1c; unfold PS_WSP in *; rewrite ?HFR in *; lia. }
(* the symbolic state at 228 *)
destruct (psa_entry W2 regs2 mem2 (pi_text D + pi_len D) (SHADOW_OFF + (pi_q D + 8) / 8) (pi_q D) (PS_SP D))
  as [HS SHOK].
{ rewrite P24, R24. unfold w64. apply unsigned_lit_small. unfold SHADOW_OFF.
  pose proof (Z.div_pos (pi_q D + 8) 8 ltac:(lia) ltac:(lia)). assert ((pi_q D + 8) / 8 <= 2 ^ 47) by (apply Z.div_le_upper_bound; lia). lia. }
{ exact HZ8. }
{ rewrite P9, R9. unfold w64. apply unsigned_lit_small. lia. }
{ exact HEND2. }
{ lia. }
{ rewrite P2, R2. unfold w64. apply unsigned_lit_small. unfold PS_Gen.PS_SP, PS_Gen.PS_FRAME in *. lia. }
{ unfold PS_Gen.PS_SP. rewrite HFR. rewrite Zminus_mod, Hal16. reflexivity. }
{ unfold PS_Gen.PS_SP. rewrite HFR. lia. }
{ intros o Ho. apply Hpres2. unfold PS_WSP, PS_WSTK, PS_Gen.PS_SP in *. rewrite HFR in *. pose proof (psc_stk_ps). lia. }
{ unfold SHADOW_OFF. pose proof (Z.div_pos (pi_q D + 8) 8 ltac:(lia) ltac:(lia)). lia. }
{ unfold PS_Gen.PS_SP. rewrite HFR. unfold SHADOW_OFF.
  assert ((pi_q D + 8) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia). lia. }
{ unfold PS_Gen.PS_SP. rewrite HFR. lia. }
{ lia. }
assert (HEI : img_env VAL A_LIM (PSA_E regs2 (pi_text D + pi_len D))) by (unfold PSA_E; apply Eimg_env).
(* the runner twins at the invariant P (laws PLAW), from HMN2 at the memory after the call *)
pose (RUN := @paj_run_x_inv fx rc SK _ PSB_PAListing PSB_PAImg B PST ARx _ LAWS P PLAW).
pose (RUNTO := @paj_run_to_x_inv fx rc SK _ PSB_PAListing PSB_PAImg B PST ARx _ LAWS P PLAW).
pose (BR := paj_branch (PI := PSB_PAImg)).
(* ---- the post state's carried facts ---- *)
pose proof psc_stk_ps as HSTK.
assert (U2 : bv_unsigned (ew (PSA_E regs2 (pi_text D + pi_len D)) 2) = PS_SP D).
{ rewrite (psa_ew_reg regs2 _ 2 2%bv eq_refl ltac:(lia)), P2, R2. unfold w64. apply unsigned_lit_small.
  unfold PS_Gen.PS_SP. rewrite HFR. lia. }
assert (Rres : 0 <= res < 2 ^ 64).
{ destruct HAP as [(_ & -> & _) | [(_ & -> & _) | (_ & Hr16 & _ & _ & _ & Eab & _)]]; [lia | lia |].
  pose proof cf_head_nonneg as Hh0.
  assert (Hin3 : In (res - cf_head, x - pi_p D + cf_head) (ablocks B ly2 S2))
    by (rewrite Eab; apply in_or_app; right; left; reflexivity).
  destruct (alx_blocks segs B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 Hin3) as (_ & _ & Hc & _).
  assert (Rq : req_size (x - pi_p D + cf_head) = x - pi_p D + cf_head)
    by (unfold req_size; destruct (Z.eqb_spec (x - pi_p D + cf_head) 0); lia).
  rewrite Rq in Hc. lia. }
assert (U10 : U (PSA_E regs2 (pi_text D + pi_len D)) (SOff 10 0) = res).
{ apply U_atom; [|exact Rres]. rewrite (psa_ew_reg regs2 _ 10 10%bv eq_refl ltac:(lia)). exact Hres. }
assert (HQ : PjGrammar.scan (ps_x D) = Some (Z.to_nat (x - (pi_p D + 1)))).
{ rewrite Heq, (psc_rest_cons (pi_tb D) (pi_text D) x 34 ltac:(lia) Hbyte). reflexivity. }
assert (Hn : Z.of_nat (Z.to_nat (x - (pi_p D + 1))) + 1 = x - pi_p D) by lia.
set (Q := Z.to_nat (x - (pi_p D + 1))) in *.
(* the old blocks survive the call, unhidden but for the harness blocks; the hidden heads grow by the new block *)
assert (Hbl : forall bm, In bm (ablocks B (pi_ly D) (pi_S D)) -> In bm (ablocks B ly2 S2)).
{ destruct HAP as [(_ & _ & _ & Eab & _) | [(_ & _ & _ & Eab & _) | (_ & _ & _ & _ & _ & Eab & _)]];
    rewrite Eab; [auto | auto | intros bm Hbm; apply in_or_app; left; exact Hbm]. }
assert (Hhp : forall h, In h (pi_Hp D) -> In h Hp2).
{ destruct HAP as [(_ & _ & EHp & _) | [(_ & _ & EHp & _) | (_ & _ & _ & _ & EHp & _)]];
    rewrite EHp; [auto | auto | intros h Hh; right; exact Hh]. }
assert (Hnh : forall p n, In (p, n) (ablocks B (pi_ly D) (pi_S D)) -> ~ In p (pi_Hp D) -> 0 <= n -> ~ In p Hp2).
{ destruct HAP as [(_ & _ & EHp & _) | [(_ & _ & EHp & _) | (_ & _ & _ & _ & EHp & Eab & _)]];
    rewrite EHp; [auto | auto |].
  intros p n Hin Hnp Hn0 [E|Hh]; [|exact (Hnp Hh)].
  pose proof cf_head_nonneg as Hh0. assert (Hm0 : 0 <= x - pi_p D + cf_head) by lia.
  exact (psc_newbase (pi_ly D) (pi_S D) ly2 S2 Hp2 W2 mem2 md2 p n (res - cf_head) (x - pi_p D + cf_head) HAR2
    Hm0 Hn0 Eab Hin (eq_sym E)). }
assert (HHp2 : forall h, In h Hp2 -> exists k, 0 <= k /\ In (h, k) (ablocks B ly2 S2)).
{ destruct HAP as [(_ & _ & _ & _ & HL2) | [(_ & _ & _ & _ & _ & _ & HL2) | (_ & _ & _ & _ & _ & _ & _ & _ & _ & HL2)]];
    exact (psc_hp_live _ _ _ _ _ _ _ _ _ _ _ _ HL2). }
pose proof HLED as (_ & _ & HLF & _).
assert (HL1 : forall b m, In (b, m) (pi_Lam D) -> 0 <= m /\ In (b - cf_head, m + cf_head) (ablocks B (pi_ly D) (pi_S D)) /\
  In (b - cf_head) (pi_Hp D)).
{ intros b m Hin. pose proof (proj1 (Forall_forall _ _) HLF _ Hin) as (Hm0 & Hab & Hhb & _).
  exact (conj Hm0 (conj Hab Hhb)). }
assert (HHOME' : prhReader_home B (pi_ly D) (pi_S D) (pi_Hp D) (pi_Lam D) (pi_text D) (Z.of_nat (length (pi_tb D))))
  by (rewrite Hlen; exact HHOME).
destruct (psb_src_after_call_nn B ARx SK LAWS ZSA IMGV _ _ _ _ _ _ _ _ _ ly2 S2 Hp2 W2 mem2 md2 k1 (pi_Lam D)
  (pi_text D) (pi_tb D) HJc HSRC HHOME') as [HSRC2 HHOME2].
{ intros a Ha. exfalso. exact (inFP_nil a Ha). }
{ exact sink_closed_nil. }
{ intros p n Hin Hnp Hn0. split; [exact (Hbl _ Hin) | exact (Hnh p n Hin Hnp Hn0)]. }
{ intros b m Hin. exact (proj1 (proj2 (HL1 b m Hin))). }
{ intros b m Hin. destruct (HL1 b m Hin) as (Hm0 & Hab & Hhb). split; [exact Hm0|].
  split; [exact (Hbl _ Hab) | exact (Hhp _ Hhb)]. }
{ exact HHp2. }
rewrite Hlen in HHOME2.
(* q's struct, the saved registers and the read-only view at the post state *)
assert (F1q : forall a, spZ (pi_regs D) <= a < 2 ^ 64 -> aview segs (w_H W2) mem2 a = aview segs (w_H (pi_W D)) mem a).
{ intros a Ha. apply F1c; unfold PS_WSP in *; rewrite ?HFR in *; lia. }
assert (HSV2 : ps_saved D W2 mem2).
{ apply (psc_saved_kept D (pi_W D) W2 mem mem2 HSAVED). intros a Ha. apply F1c; unfold PS_WSP, PS_Gen.PS_SP in *;
  rewrite ?HFR in *; lia. }
assert (HPJ2 : pj_in_okR segs (rdW W2 mem2) (pi_q D) (pi_text D) (pi_len D) (pi_p D) (pi_d D) (pi_tb D)).
{ apply (psc_pj_kept (pi_W D) W2 mem mem2 _ _ _ _ _ _ HPJ).
  - intros a Ha. apply F1q. lia.
  - intros a Ha. apply Hpres2. unfold PS_WSP, PS_WSTK. lia.
  - exact (proj1 HSRC2). }
assert (HROD2 : arodata_okP segs pa_relro_lo pa_relro_hi B (aview segs (w_H W2) mem2)).
{ apply (psc_rod_kept (pi_W D) W2 mem mem2 HROD). intros a Hi Hno He Hp. apply F3c; [exact Hi | exact Hno | exact He | exact Hp |].
  apply fp_spares_closed. exact sink_closed_nil. }
assert (K_ep : KEPT STK_parse_string (spZ (pi_regs D)) [(pi_q D, pi_q D + 8)] [] (pi_ly D) (pi_S D) (pi_W D)
  (pi_mem D) (pi_md D) ly2 S2 W2 mem2 md2).
{ eapply (cj_kept_trans (SK := SK) segs B PST ARx LAWS); [exact HKEPT | | exact HAR0 | exact (ajx_ar HJ) | | | |].
  - eapply (cj_kept_of_journal (SK := SK) segs B PST ARx). exact HJc.
  - unfold PS_WSP. rewrite HFR. lia.
  - unfold PS_WSP. rewrite HFR. lia.
  - intros a Ha. exfalso. exact (inFP_nil a Ha).
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
pose proof HJ2 as HJ2c.
pose proof HLED as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & Hcnt0 & _) & _).
assert (Hcnt1 : (pi_cnt D + 1) mod 2 ^ 64 = pi_cnt D + 1) by (apply Z.mod_small; lia).
destruct (pal_env B TL) as ((Herr0 & Herr4) & _ & _).
assert (HSPlo : YM05.alloc_ceiling + 144 <= spZ (pi_regs D)) by lia.
(* the facts every arm's final state reads below alloc_ceiling and in q's struct are the post state's *)
assert (Hlow : forall a, 0 <= a < YM05.alloc_ceiling -> ~ (PS_SP D + 8 <= a < PS_SP D + 32))
  by (intros a Ha; unfold PS_Gen.PS_SP; rewrite HFR; lia).
assert (Hqhi' : forall a, pi_q D <= a < pi_q D + 24 -> 0 <= a < 2 ^ 64 /\ ~ (PS_SP D + 8 <= a < PS_SP D + 32))
  by (intros a Ha; unfold PS_Gen.PS_SP; rewrite HFR; lia).
psrr_branch_tok RUN BR HS SHOK PSC_Bspan.
- (* a0 = 0: the two refusing arms (the chosen failure, the allocator's refusal); `beqz a0` to PSB_RET0 *)
  rewrite branch_eq_U, U10, U_SLit in Hc. change (zcanon 0) with 0 in Hc. apply Z.eqb_eq in Hc. subst res.
  paj_run_to_tok_x_inv RUNTO HS HJ2 SHOK HMN2 PSC_Bspan (PSB_OFF + PSB_RET0).
  + psa_awr D U2.
  + (* at PSB_RET0 (offset 1256): the refusing arms' return; the run wrote no byte the post state reads *)
    assert (HFW : forall x0 : word, ~ (PS_SP D + 8 <= bv_unsigned x0 < PS_SP D + 32) ->
      mrestrict (w_H W2) (ms_mem ms) x0 = mrestrict (w_H W2) mem2 x0).
    { intros x0 Hx0. apply HFr. intros (r & Hin & Hr). cbn in Hin.
      destruct Hin as [<-|[<-|[<-|[]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; [lia | lia |].
      rewrite U2 in Hr. lia. }
    pmkst HS. psc_at PSB_RET0.
    destruct (psc_final CTX CW D ly2 S2 Hp2 W2 mem2 md2 (ms_mem ms) _ _ (0 + k1) HPRE HJ2 HJ2c K_ep HFW
      (same_but_materialized_wvb_any _ _) HSV2 HSRC2 HHOME2 HMN2) as [HCF KF].
    pose proof HCF as (_ & _ & _ & HSRCF & _).
    pose proof (ajx_pres HJ2) as HpresF.
    assert (K2 : getr (ms_regs ms) 2 = getr regs2 2) by psa_kr HS.
    assert (K3 : getr (ms_regs ms) 3 = getr regs2 3) by psa_kr HS.
    assert (K4 : getr (ms_regs ms) 4 = getr regs2 4) by psa_kr HS.
    assert (KL : forall a, 0 <= a < YM05.alloc_ceiling -> aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) mem2 a)
      by (intros a Ha; apply KF; [lia | exact (Hlow a Ha)]).
    assert (HPJF : pj_in_okR segs (rdW W2 (ms_mem ms)) (pi_q D) (pi_text D) (pi_len D) (pi_p D) (pi_d D) (pi_tb D)).
    { apply (psc_pj_kept W2 W2 mem2 (ms_mem ms) _ _ _ _ _ _ HPJ2).
      - intros a Ha. destruct (Hqhi' a Ha) as [Ha1 Ha2]. exact (KF a Ha1 Ha2).
      - intros a Ha. apply HpresF. unfold PS_WSP, PS_WSTK. lia.
      - exact (proj1 HSRCF). }
    apply ps_finP_of_postP. apply (HRET0 D ly2 S2 Hp2 W2 _ _ _ HPRE).
    split; [exists (0 + k1), []; split; [apply ps_wb_nil | exact HCF]|].
    split; [unfold ps_gptp; rewrite K3, K4, P3, P4; exact HGP|].
    split; [rewrite K2, P2; exact R2|].
    split; [exact HRL2|].
    split.
    { rewrite (blocks_bytes_bsum B ly2 S2), (blocks_bytes_bsum B (pi_ly D) (pi_S D)).
      pose proof (psc_held_nonneg (ps_x D)).
      destruct HAP as [(_ & _ & _ & Eab & _) | [(_ & _ & _ & Eab & _) | (_ & Hr16 & _)]];
        [rewrite Eab; lia | rewrite Eab; lia | pose proof cf_head_nonneg; lia]. }
    unfold ps_Qres. rewrite HQ.
    destruct HAP as [(Hcf & _ & EHp & Eab & HL2) | [(Hcf & _ & EHp & Eab & Hnull & Herr & HL2) | (_ & Hr16 & _)]].
    * left. split; [exact Hcf|]. split; [reflexivity|]. split; [exact EHp|]. split; [exact Eab|].
      split; [|split; [exact HPJF | exact (HRP0 ltac:(assumption))]].
      rewrite Hcnt1 in HL2. exact (psc_ledger_low ly2 S2 Hp2 W2 mem2 (ms_mem ms) mem2 md2 _ _ _ _ _ _ _ HAR2 HL2 KL).
    * right; left. split; [exact Hcf|]. split; [reflexivity|]. split; [exact EHp|]. split; [exact Eab|].
      split; [rewrite Hn; exact Hnull|].
      split; [intros kk Hkk; rewrite KL; [exact (Herr kk Hkk) | cbn in Hkk; lia]|].
      (* the batch text's outcome exclusion (PRH_FnReader f1ae32e3b2cd :625-629), from the malloc's outcome clause *)
      split; [exact (HEX ltac:(assumption) Hcf)|].
      (* the ledger: the callee's refusal arm VERBATIM, the count `(cnt + 1) mod 2 ^ 64` kept (:633-635) *)
      split; [|split; [exact HPJF | exact (HRP0 ltac:(assumption))]].
      rewrite <- Hn in HL2. exact (psc_ledger_low ly2 S2 Hp2 W2 mem2 (ms_mem ms) mem2 md2 _ _ _ _ _ _ _ HAR2 HL2 KL).
    * exfalso. pose proof cf_head_nonneg. lia.
- (* a0 <> 0: the success arm *)
  rewrite branch_eq_U, U10, U_SLit in Hc. change (zcanon 0) with 0 in Hc. apply Z.eqb_neq in Hc.
  paj_run_tok_x_inv RUN HS HJ2 SHOK HMN2 PSC_Bspan.
  + psa_awr D U2.
  + (* at `bgeu s4, a0` (offset 248): p + 1 < end, NOT taken (the closing quote is before end) *)
    psrr_branch_tok RUN BR HS SHOK PSC_Bspan.
    * exfalso. rewrite branch_geu_U in Hc0.
      assert (U20 : U (PSA_E regs2 (pi_text D + pi_len D)) (SOff 20 0) = pi_p D + 1).
      { apply U_atom; [|lia]. rewrite (psa_ew_reg regs2 _ 20 20%bv eq_refl ltac:(lia)), P20. exact R20. }
      assert (U32 : U (PSA_E regs2 (pi_text D + pi_len D)) (SOff 32 0) = pi_text D + pi_len D).
      { apply U_atom; [apply psa_ew_end | lia]. }
      rewrite U20, U32 in Hc0. apply negb_true_iff, Z.ltb_ge in Hc0. lia.
    * paj_run_to_tok_x_inv RUNTO HS HJ2 SHOK HMN2 PSC_Bspan (PSB_OFF + PSB_DEC).
      -- psa_awr D U2.
      -- (* at PSB_DEC (offset 324): s2 = s3 = out, s4 = p + 1, a0 = end, the constants and the surrogate words *)
         assert (HFW : forall x0 : word, ~ (PS_SP D + 8 <= bv_unsigned x0 < PS_SP D + 32) ->
           mrestrict (w_H W2) (ms_mem ms0) x0 = mrestrict (w_H W2) mem2 x0).
         { intros x0 Hx0. transitivity (mrestrict (w_H W2) (ms_mem ms) x0); [apply HFr0 | apply HFr];
             intros (r & Hin & Hr); cbn in Hin; destruct Hin as [<-|[<-|[<-|[]]]];
             cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; [lia | lia | rewrite U2 in Hr; lia
                                                                    | lia | lia | rewrite U2 in Hr; lia]. }
         pmkst HS. psc_at PSB_DEC.
         rewrite !wvb_collapse in HJ2.
         destruct (psc_final CTX CW D ly2 S2 Hp2 W2 mem2 md2 (ms_mem ms0) _ _ (0 + k1) HPRE HJ2 HJ2c K_ep HFW
           (same_but_materialized_wvb_any _ _) HSV2 HSRC2 HHOME2 HMN2) as [HCF KF].
         pose proof HCF as (_ & _ & _ & HSRCF & _).
         pose proof (ajx_pres HJ2) as HpresF.
         assert (KL : forall a, 0 <= a < YM05.alloc_ceiling ->
           aview segs (w_H W2) (ms_mem ms0) a = aview segs (w_H W2) mem2 a)
           by (intros a Ha; apply KF; [lia | exact (Hlow a Ha)]).
         assert (HPJF : pj_in_okR segs (rdW W2 (ms_mem ms0)) (pi_q D) (pi_text D) (pi_len D) (pi_p D) (pi_d D)
           (pi_tb D)).
         { apply (psc_pj_kept W2 W2 mem2 (ms_mem ms0) _ _ _ _ _ _ HPJ2).
           - intros a Ha. destruct (Hqhi' a Ha) as [Ha1 Ha2]. exact (KF a Ha1 Ha2).
           - intros a Ha. apply HpresF. unfold PS_WSP, PS_WSTK. lia.
           - exact (proj1 HSRCF). }
         (* the registers at DEC *)
         assert (K2 : getr (ms_regs ms0) 2 = getr regs2 2) by psa_kr HS.
         assert (K3 : getr (ms_regs ms0) 3 = getr regs2 3) by psa_kr HS.
         assert (K4 : getr (ms_regs ms0) 4 = getr regs2 4) by psa_kr HS.
         assert (K8 : getr (ms_regs ms0) 8 = getr regs2 8) by psa_kr HS.
         assert (K9 : getr (ms_regs ms0) 9 = getr regs2 9) by psa_kr HS.
         assert (K18 : getr (ms_regs ms0) 18 = getr regs2 10) by psa_kr HS.
         assert (K19 : getr (ms_regs ms0) 19 = getr regs2 10) by psa_kr HS.
         assert (K20 : getr (ms_regs ms0) 20 = getr regs2 20) by psa_kr HS.
         assert (K22 : getr (ms_regs ms0) 22 = getr regs2 22) by psa_kr HS.
         assert (K23 : getr (ms_regs ms0) 23 = getr regs2 23) by psa_kr HS.
         assert (K24 : getr (ms_regs ms0) 24 = getr regs2 24) by psa_kr HS.
         assert (K10 : getr (ms_regs ms0) 10 = w64 (pi_text D + pi_len D)).
         { rewrite (st_ok_pi_restrict_reg _ _ _ _ (10%bv : bv 5) HS).
           lazymatch goal with |- sv_denot ?E (sr_get ?sr ?r) = _ =>
             let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
           cbn [sv_denot]. rewrite psa_ew_end, Z.add_0_r, unsigned_lit_small by lia. reflexivity. }
         assert (D25 : getr (ms_regs ms0) 25 = w64 34) by psa_lit HS.
         assert (D26 : getr (ms_regs ms0) 26 = w64 (-1)) by psa_lit HS.
         assert (D27 : getr (ms_regs ms0) 27 = w64 92) by psa_lit HS.
         assert (D14 : getr (ms_regs ms0) 14 = w64 32) by psa_lit HS.
         assert (D15 : getr (ms_regs ms0) 15 = w64 101) by psa_lit HS.
         assert (D16 : getr (ms_regs ms0) 16 = w64 91) by psa_lit HS.
         assert (D17 : getr (ms_regs ms0) 17 = w64 113) by psa_lit HS.
         assert (D5 : getr (ms_regs ms0) 5 = w64 114) by psa_lit HS.
         (* the three surrogate words in the frame region *)
         pose proof (st_ok_region_nth segs _ _ _ 2 _ HS eq_refl) as HR2.
         pose proof (slot_of_region segs _ _ _ _ _ _ _ _ 24 (SLit 55296) 55296 HR2 U2
           ltac:(cbn; right; right; left; reflexivity) eq_refl ltac:(lia)) as SL24.
         pose proof (slot_of_region segs _ _ _ _ _ _ _ _ 16 (SLit 56320) 56320 HR2 U2
           ltac:(cbn; left; reflexivity) eq_refl ltac:(lia)) as SL16.
         pose proof (slot_of_region segs _ _ _ _ _ _ _ _ 8 (SLit (2 ^ 64 - 56613888)) (2 ^ 64 - 56613888) HR2 U2
           ltac:(cbn; right; left; reflexivity) eq_refl ltac:(lia)) as SL8.
         apply (psc_val_mem_mod _ _ _ (-56613888) ltac:(reflexivity)) in SL8.
         (* the success arm *)
         destruct HAP as [(_ & Hr0 & _) | [(_ & Hr0 & _) | (Hcf & Hr16 & Hral & HnotLam & EHp & Eab & HRA3 & HHU3 & Hby3 & HL3)]];
           [exfalso; exact (Hc Hr0) | exfalso; exact (Hc Hr0) |].
         pose proof cf_head_nonneg as Hh0.
         assert (Hin3 : In (res - cf_head, x - pi_p D + cf_head) (ablocks B ly2 S2))
           by (rewrite Eab; apply in_or_app; right; left; reflexivity).
         destruct (alx_blocks segs B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 Hin3) as (_ & _ & Hblk & _).
         assert (Rq : req_size (x - pi_p D + cf_head) = x - pi_p D + cf_head)
           by (unfold req_size; destruct (Z.eqb_spec (x - pi_p D + cf_head) 0); lia).
         rewrite Rq in Hblk.
         apply ps_finP_hand. apply (HDEC D ly2 S2 Hp2 W2 _ _ _ res res (pi_p D + 1) Q HPRE).
         split; [exists (0 + k1); exact HCF|].
         split.
         { unfold ps_alloc. split; [exact Hcf|]. split; [exact Hr16|]. split; [exact Hral|]. split; [exact EHp|].
           split; [rewrite Eab, <- Hn; reflexivity|].
           split; [rewrite <- Hn, Hcnt1 in HL3; exact (psc_ledger_low ly2 S2 Hp2 W2 mem2 (ms_mem ms0) mem2 md2 _ _ _ _ _ _ _
             HAR2 HL3 KL)|].
           split; [rewrite Hn; apply (psc_vis_low W2 mem2 (ms_mem ms0) res (x - pi_p D) (conj HRA3 HHU3)); [lia | lia | lia | exact KL]|].
           split; [exact HRL2|].
           split; [unfold PS_Gen.ps_rpos_mal; rewrite Hn; apply HRPM; pose proof cf_head_nonneg as Hhnn; clear - Hr16 Hhnn; lia|].
           rewrite (blocks_bytes_bsum B ly2 S2), (blocks_bytes_bsum B (pi_ly D) (pi_S D)), Eab, bsum_app.
           cbn [bsum fold_right snd]. lia. }
         split; [unfold psb_sh_regs; rewrite K23, K22, K24, P23, P22, P24; exact (conj R23 (conj R22 R24))|].
         split; [unfold ps_gptp; rewrite K3, K4, P3, P4; exact HGP|].
         split.
         { unfold psb_dec_consts. split; [exact D25|]. split; [exact D26|]. split; [exact D27|].
           split; [exact D14|]. split; [exact D15|]. split; [exact D16|]. split; [exact D17|]. split; [exact D5|].
           split; [exact SL24|]. split; [exact SL16 | exact SL8]. }
         split; [exact HPJF|].
         split.
         { apply (psc_rod_kept W2 W2 mem2 (ms_mem ms0) HROD2). intros a Hi _ _ _.
           pose proof (@pa_segs_low _ _ PSB_PAImg a Hi). apply KL. lia. }
         split; [exact HQ|].
         split; [rewrite K2, P2; exact R2|].
         split; [rewrite K18; exact Hres|].
         split; [rewrite K19; exact Hres|].
         split; [rewrite K20, P20; exact R20|].
         split; [exact K10|].
         split; [rewrite K8, P8; exact R8|].
         split; [rewrite K9, P9; exact R9|].
         exists []. split; [apply garr8_nil|]. split; [cbn; lia|].
         split; [intros sx rx Hd; exact Hd|]. split; [intros Hd; exact Hd|].
         split; [lia|]. split; [lia|]. split; [lia|].
         replace (Z.to_nat (pi_p D + 1 - (pi_p D + 1))) with 0%nat by lia. rewrite Nat.sub_0_r. exact HQ.
Qed.

(* THE FOUND PATH: the byte at the cursor is the closing quote; 148 .. 224 (`jal fuzz_malloc`); P after the call is the
   cut's P at the call memory carried by the callee text's memnorm keep (its m-form post) through PCALL. The position
   after the call (POST-IMPLICATION): fuzz_malloc's NULL arm transfers every position by E = [], its block
   arm by HMal (Q + 1 + cf_head); no agreement premise (the implications are applied at the run the caller picks) *)
Lemma psc_found : forall CTX CW (D : ps_in), psb_seg_ret0P B ARx SK CTX CW P -> psb_seg_decP B ARx SK CTX CW P ->
  ps_pre CTX CW D -> psc_found_at CTX CW D.
Proof.
intros CTX CW D HRET0 HDEC HPRE regs mem md x HAT Hbyte.
pose proof HAT as (HC & HSH & HGP & _ & _ & _ & _ & HLED & HPJ & HROD & R2 & R10 & R11 & R12 & R8 & R9 & R20 & Hx & Heq).
pose proof HC as (HJ & HKEPT & HSAVED & HSRC & HHOME & HMN).
pose proof HPJ as (_ & _ & _ & _ & _ & Htpos & Htlen & Hple & Hlen & _).
pose proof HSRC as (HBY & Ht4096 & Htceil & Htamr & HRA & _).
pose proof asan_consts as (C1 & _).
assert (Hx47 : x < 2 ^ 47) by lia.
destruct (psc_entry D (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) regs mem md x 34 HAT Hbyte) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (PSC_E regs 34)) by (unfold PSC_E; apply Eimg_env).
(* the runner twin at the invariant P (laws PLAW), from the cut's HMN *)
pose (RUN := @paj_run_x_inv fx rc SK _ PSB_PAListing PSB_PAImg B PST ARx _ LAWS P PLAW).
pose (BR := paj_branch (PI := PSB_PAImg)).
unfold cfg_at, psb_pc, w64. rewrite <- Z.add_assoc.
paj_run_tok_x_inv RUN HS HJ SHOK HMN PSC_Bspan.
- cbn [ms_mem mkst]. rewrite (psc_U_Bx D regs 34 HSH), (psc_U_x regs 34 x R10 ltac:(lia)).
  eapply range_addressable_sub; [exact HRA | lia | lia].
- unfold ss_psc, psc_regions. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil].
- assert (Emem : ms_mem ms = mem) by psc_mem_id.
  psrr_branch_tok RUN BR HS SHOK PSC_Bspan.
  + (* the quote: to 216, the length and the call *)
    clear Hc. paj_run_tok_x_inv RUN HS HJ SHOK HMN PSC_Bspan.
    * intros a (r & Hin & Ha). cbn in Hin. destruct Hin as [<-|[]]. cbn in Ha. lia.
    * (* the call `jal fuzz_malloc` (offset 224): n = x - p = Q + 1 *)
      assert (Emem0 : ms_mem ms0 = mem) by (rewrite <- Emem; psc_mem_id).
      rewrite !wvb_collapse in HJ.
      pose proof HPRE as (HFP & HCL & _ & _ & _ & HGAP & HRL & HRP & HREVS & _ & HPJ0 & _ & _ & HWIN & Hqlo & Hqhi & _ &
        _ & _ & _ & HCNT & HLIVE).
      pose proof HFP as (HAFN & _ & Htop64).
      pose proof HAFN as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & _ & HQT0).
      pose proof Hstk0 as (Hal16 & HSTK0 & Hceil0 & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
      pose proof HWIN as (He0 & He16 & Hetop & Hepres).
      pose proof psc_frame as HFR. pose proof psc_stk_ps as HSTK.
      pose proof (@pa_B_ok _ _ PSB_PAImg) as HBASE.
      assert (Rsp : 2 ^ 46 <= spZ (pi_regs D) <= 2 ^ 47) by lia.
      (* the scan's answer: Q bytes before the quote *)
      assert (HQ : PjGrammar.scan (ps_x D) = Some (Z.to_nat (x - (pi_p D + 1)))).
      { rewrite Heq, (psc_rest_cons (pi_tb D) (pi_text D) x 34 ltac:(lia) Hbyte). reflexivity. }
      assert (Hn : Z.of_nat (Z.to_nat (x - (pi_p D + 1))) + 1 = x - pi_p D) by lia.
      (* the registers at the call: the callee-saved ones are the scan's *)
      assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 34]) (ewset (ewset (PSC_E regs 34) 512 w) 513 w0)).
      { split; [intros n Hn'; rewrite !ew_ewset_other by lia; unfold PSC_E; apply Eimg_low; unfold A_TEXT; lia
               | reflexivity]. }
      pose proof (aregs_preserved_of_st_ok segs _ _ _ _ regs [Z_to_bv 64 34] HS HAE ltac:(vm_compute; reflexivity))
        as HPsc.
      assert (C2 : getr (ms_regs ms0) 2 = getr regs 2) by psc_pres HPsc.
      assert (C3 : getr (ms_regs ms0) 3 = getr regs 3) by psc_pres HPsc.
      assert (C4 : getr (ms_regs ms0) 4 = getr regs 4) by psc_pres HPsc.
      assert (C8 : getr (ms_regs ms0) 8 = getr regs 8) by psc_pres HPsc.
      assert (C10 : getr (ms_regs ms0) 10 = w64 (Z.of_nat (Z.to_nat (x - (pi_p D + 1))) + 1)).
      { rewrite (st_ok_restrict_reg segs _ _ _ _ 10%bv HS). rewrite denot_lit_U. unfold w64. f_equal. rewrite Hn.
        apply psc_len_U; [| | lia | lia].
        - rewrite psc_ew_ext2 by lia. rewrite (psc_ew_reg regs 34 10 10%bv eq_refl ltac:(lia)). exact R10.
        - rewrite psc_ew_ext2 by lia. rewrite (psc_ew_reg regs 34 20 20%bv eq_refl ltac:(lia)). exact R20. }
      prreg HS (1%bv : bv 5) RA1.
      lazymatch type of RA1 with _ = Z_to_bv 64 (_ + ?k) =>
        assert (Ek : k = PSB_OFF + PSC_RET) by (vm_compute; reflexivity); rewrite Ek in RA1 end.
      assert (HKr : (0 <=? PSB_OFF + PSC_RET) && (PSB_OFF + PSC_RET <? 2 ^ 40) = true) by (vm_compute; reflexivity).
      apply andb_true_iff in HKr as [HKr1 HKr2]. apply Z.leb_le in HKr1. apply Z.ltb_lt in HKr2.
      (* the chain from q at the call view: the entry view off the caller word *)
      assert (Hview : forall a, spZ (pi_regs D) <= a < 2 ^ 64 -> ~ (pi_q D <= a < pi_q D + 8) ->
                aview segs (w_H (pi_W D)) (ms_mem ms0) a = aview segs (w_H (pi_W D)) (pi_mem D) a).
      { intros a Ha Hq. rewrite Emem0. pose proof HKEPT as (_ & _ & _ & _ & _ & K1 & _).
        apply K1; [lia | lia |]. rewrite inFP_cons. intros [Hx1 | Hx1]; [lia | exact (inFP_nil _ Hx1)]. }
      destruct (ps_chain_call_offq (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg) B ARx CTX CW D
        (aview segs (w_H (pi_W D)) (ms_mem ms0)) HPRE
        ltac:(rewrite psb_s0_q; lia) ltac:(rewrite psb_s0_q; lia) ltac:(lia) Hview) as (ch1 & Hch1).
      rewrite psb_s0_q in Hch1.
      assert (HATc : psb_at_scanP B ARx SK P D (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) regs mem
                       (with_vm_backing (m_vm_lazy md) mat0 md) x).
      { destruct HAT as (_ & HREST). split; [|exact HREST].
        split; [rewrite <- Emem0; exact HJ|]. split; [apply psc_kept_wvb; exact HKEPT|].
        split; [exact HSAVED|]. split; [exact HSRC|]. split; [exact HHOME|]. rewrite <- Emem0. exact HMN. }
      eapply SRr_bind.
      { eapply (aj_call_x_sp (SK := SK) segs B PST ARx LAWS (@pa_segs_low _ _ PSB_PAImg) (pi_W D) _ _ ms0
          (PS_WSTK D) (PS_WSP D) [(pi_q D, pi_q D + 8)] (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) []
          (pi_ly D) (pi_S D) (pi_Hp D) _ 0 STK_fuzz_malloc [] (- pi_e D - PS_FRAME) _ ch1 _ HS eq_refl HJ).
        - unfold spZ at 1. rewrite C2, R2. unfold w64.
          rewrite unsigned_lit_small by (unfold PS_Gen.PS_SP; lia). unfold PS_Gen.PS_SP, PS_WSP. lia.
        - rewrite HFR. pose proof (Z.div_mod (pi_e D) 16 ltac:(lia)) as Hd. rewrite He16, Z.add_0_r in Hd.
          rewrite Hd. replace (- (16 * (pi_e D / 16)) - 144) with ((- (pi_e D / 16) - 9) * 16) by ring.
          apply Z_mod_mult.
        - lia.
        - lia.
        - unfold PS_WSTK. lia.
        - rewrite C3. destruct HGP as [G3 _]. rewrite G3. exact Hgp0.
        - rewrite C4. destruct HGP as [_ G4]. rewrite G4. exact Htp0.
        - exact RA1.
        - apply (ret_ok_codeptr_v (PI := PSB_PAImg)); [lia | vm_compute; reflexivity].
        - assert (HB4 : (4096 <=? BASE + (PSB_OFF + PSC_RET)) && (BASE + (PSB_OFF + PSC_RET) <? 2 ^ 64) = true)
            by (vm_compute; reflexivity).
          apply andb_true_iff in HB4 as [HB41 HB42]. apply Z.leb_le in HB41. apply Z.ltb_lt in HB42.
          rewrite unsigned_lit_small by lia. lia.
        - unfold s0Z. rewrite C8, R8. unfold w64. rewrite unsigned_lit_small by lia.
          replace (PS_WSP D + (- pi_e D - PS_FRAME)) with (spZ (pi_regs D) - pi_frame F_parse_string)
            by (unfold PS_WSP, PS_Gen.PS_FRAME; lia).
          exact Hch1.
        - intros HPRE1.
          refine (psc_malloc_text CTX CW D _ _ _ _ _ HPRE HQ HPRE1 _ _ _ C10 _).
          + rewrite Emem0. exact HROD.
          + unfold spZ at 1. rewrite C2, R2. unfold w64.
            rewrite unsigned_lit_small by (unfold PS_Gen.PS_SP; lia). unfold PS_Gen.PS_SP. lia.
          + (* the return address is the jal's return pc, a listing slot: below 2 ^ 46, so below CEIL_MIN *)
            unfold raZ. rewrite RA1. pose proof YM05.alloc_ceiling_value as Hcv.
            assert (HB5 : (4096 <=? BASE + (PSB_OFF + PSC_RET)) && (BASE + (PSB_OFF + PSC_RET) <? 2 ^ 46) = true)
              by (vm_compute; reflexivity).
            apply andb_true_iff in HB5 as [HB51 HB52]. apply Z.leb_le in HB51. apply Z.ltb_lt in HB52.
            rewrite unsigned_lit_small by lia. lia.
          + rewrite Emem0. exact HLED.
        - intros a (r & Hr & _). destruct Hr. }
      cbv beta. intros W2 c2 Hwle (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HJc & HP2 & HKC & HKEEP).
      cbv beta delta [psc_malloc_KC] in HKC.
      (* P after the call: the cut's P at the call memory, carried by the callee text's memnorm keep (fQmn) through
         PCALL *)
      assert (HMN2 : P mem2)
        by (apply (PCALL _ mem2 HKEEP); first [exact HMN | (rewrite <- Emem0; exact HMN)]).
      destruct HKC as (res & Hres & HRL2 & HHU & HKP & HAD & HOUT & HAP).
      (* the call's hull use, read at the all-granted list: the use part of both transfers below *)
      pose proof (ps_hull_used_mal (L := B_prog_listing) (PA := PSB_PAImg) D (Z.to_nat (x - (pi_p D + 1))) S2 HQ HHU)
        as HHU2.
      (* the refused arm's outcome exclusion, from the malloc's outcome clause *)
      assert (HEX : res = 0 -> pi_cnt D <> pi_fail D -> ps_excl D)
        by (intros Hr Hcf; exact (ps_excl_of_malloc D (Z.to_nat (x - (pi_p D + 1))) S2 res HQ Hcf Hr HOUT)).
      (* the position after the call: the post's own implications, a NULL's E = [] and a block's HMal (n + cf_head) *)
      assert (HRP0 : res = 0 -> ps_rpos D [] S2) by (intros Hr; exact (conj HHU2 (HKP Hr))).
      assert (HRPM : res <> 0 -> ps_rpos D [PresetReqAt.HMal (x - pi_p D + cf_head)] S2)
        by (intros Hr; split; [exact HHU2|]; rewrite <- Hn; exact (HAD Hr)).
      rewrite Hn in HAP. rewrite Emem0 in HJc.
      exact (psc_post_call CTX CW D regs mem _ x (ms_regs ms0) W2 ly2 S2 Hp2 regs2 mem2 md2 k1 res HRET0 HDEC HPRE
        HATc Hbyte HPsc HJ2 HJc HP2 Hres HRL2 HRP0 HRPM HEX HAP HMN2).
  + (* not the quote: excluded, the byte is 34 *)
    exfalso. rewrite branch_eq_U in Hc.
    rewrite (U_atom _ 32 34), (U_atom _ 12 34) in Hc.
    * rewrite Z.eqb_refl in Hc. discriminate Hc.
    * rewrite psc_ew_ext2 by lia. rewrite (psc_ew_reg regs 34 12 12%bv eq_refl ltac:(lia)). exact R12.
    * lia.
    * rewrite psc_ew_ext2 by lia. apply psc_ew_byte.
    * lia.
Qed.

(* THE STRETCH OVER P: every premise of the call step is the call state's or the entry's; P across the call is the
   callee text's keep through PCALL *)
Lemma psc_scan_of : forall CTX CW, psb_seg_ret0P B ARx SK CTX CW P -> psb_seg_decP B ARx SK CTX CW P ->
  psb_seg_scanP B ARx SK CTX CW P.
Proof.
intros CTX CW HRET0 HDEC D ly S Hp W regs mem md x HPRE HAT.
pose proof HAT as (_ & _ & _ & Hly & HS & HHp & HW & _). subst ly S Hp W.
apply ps_finP_SRr'.
exact (psc_loop CTX CW D HRET0 HPRE (psc_found CTX CW D HRET0 HDEC HPRE)
  (Z.to_nat (pi_text D + pi_len D - x)) x regs mem md (le_n _) HAT).
Qed.
End scP.

(* ---- THE STRETCH IN THE GENERIC-P FORM (a Theorem Labs lane 12:18Z / 12:22Z): over any invariant P with its runner laws and,
   since the stretch crosses the fuzz_malloc call, srr_inv_call segs P (the callee text's m-form post gives the memnorm
   keep). No open premise: the live counts are ps_pre's peaks, the position the post's implications ---- *)
Theorem psb_scan_holdsP : forall CTX CW (P : (word -> option byte) -> Prop),
  srr_inv_laws segs P -> srr_inv_call segs P ->
  psb_seg_ret0P B ARx SK CTX CW P -> psb_seg_decP B ARx SK CTX CW P ->
  psb_seg_scanP B ARx SK CTX CW P.
Proof. intros CTX CW P PLAW PCALL. exact (psc_scan_of P PLAW PCALL CTX CW). Qed.

(* ---- THE STRETCH STATEMENT of PSB_Base (psb_seg_scan, the other stretches as hypotheses): the P := (fun _ => True)
   instance of psb_scan_holdsP ---- *)
Theorem psb_scan_holds : forall CTX CW,
  psb_seg_ret0 B ARx SK CTX CW -> psb_seg_dec B ARx SK CTX CW -> psb_seg_scan B ARx SK CTX CW.
Proof.
intros CTX CW HRET0 HDEC.
apply (proj1 (psb_seg_scan_of_True B ARx SK CTX CW)).
apply (psb_scan_holdsP CTX CW (fun _ => True) srr_inv_laws_True srr_inv_call_True).
- exact (proj2 (psb_seg_ret0_of_True B ARx SK CTX CW) HRET0).
- exact (proj2 (psb_seg_dec_of_True B ARx SK CTX CW) HDEC).
Qed.

End psc.
