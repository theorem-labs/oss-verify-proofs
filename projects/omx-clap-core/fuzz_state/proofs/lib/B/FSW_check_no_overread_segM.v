(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFl3.v:106-108
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:383-389, 448-454, 493-498, 501-509 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:625-631 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:208-214, 227-233 [Apache-2.0 OR MIT], for libreac/fuzz_identity's ASan
   build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_name_seg10.v, with its module paths and module names changed; 2634 of its 2686 lines of code are new or changed and 608 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSH_parse_value.v, with its module paths, module names, addresses and numbers changed; 1014 of its 1163 lines of code are new or changed and 2537 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_check_no_overread.v, with its module paths and module names changed; 1341 of its 1416 lines of code are new or changed and 1088 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_check_no_overread_top.v, with its module paths, module names and addresses changed; 1416 of its 1530 lines of code are new or changed and 1302 lines of the source are left out. *)
(* check_no_overread B 0x8124c (fs.c), fs.asan-ubsan: the FIRST span of the walk, segM_T of
   lib/B/FSW_check_no_overread_inv.v: from the return of __wrap_malloc (0x813a0, the symbolic boundary ss_M / INV_M)
   to the machine at the first preset_base64_decode call (INV_D1). Owner a Theorem Labs lane.
   MEASURED range (neutral_dis listing (internal path),
   lines 87-128, re-read by this lane):
   - 0x813a0 `beqz a0, 0x815f4`: UNTAKEN (cno_call_mal's post t <> 0, and the walk's own atom fact 4096 <= t from
     YCbq.al_blocks: the abort block is not reached);
   - 0x813a4 `mv s5,a0`; 0x813a8 `beqz s6`: the two arms n = 0 (skip) and n > 0 (__asan_memcpy 0x813b8, ra 0x813bc);
     both reach 0x813bc with s5 = t (the walk's atom 10), so ss_C is their common symbolic state;
   - 0x813bc `not s7,s5`; U1 0x813c0 `bltu s7,s6`: UNTAKEN. s7 = ~t is the walk's atom 55 with range
     [2 ^ 64 - 1 - 2 ^ 47, 2 ^ 64 - 1] (t < 2 ^ 47: the block lies in application memory, YCbq.al_blocks under the
     journal's AR) and s6 = n <= PRESET_FILE_MAX_BYTES = 3 * 2 ^ 20 (cno_base), so the engine decides it;
   - 0x813c4-0x813d4 the inline ASan check of the 1-byte store at x1 = t + n: the shadow byte is the walk's atom 54
     with range [0, 7], read from the block's own shadow (cno_call_mal's post range_addressable [t, t + n + 18),
     kept by __asan_memcpy). Two arms: 00 (fall through) and non-zero (slow path 0x81600 `andi a2,a0,7`,
     0x81604 `blt a2,a1` TAKEN back to 0x813d8 by saddr_ok x1 s: x1 mod 8 < s). Both reach 0x813d8;
   - 0x813dc `sb zero,0(a0)` stores t[n] = 0; U2 0x813e0 `beq a0,-1`: UNTAKEN (t + n < 2 ^ 48);
   - 0x813e4-0x813f0 s6 := n + 17, a0 := t + n + 1, a2 := 16, a1 := 0; 0x813f4 __asan_memset (t + n + 1, 0, 16)
     (ra 0x813f8, the resume state ss_S);
   - U3 0x813f8 `bltu s7,s6` with s6 = n + 17: UNTAKEN, as U1; 0x813fc `sd s9,16(s1)` puts the frame address in the
     slot 0x10; 0x81400-0x81410 the second inline check, at x2 = t + n + 17 (slow path 0x8160c, report 0x81614),
     the same two arms, both reaching 0x81414;
   - 0x81414-0x8141c s10 / s7 / s11 := F + 0x20 / 0x40 / 0x60; 0x81420 `sb zero,0(a0)` stores t[n + 17] = 0;
     0x81424 / 0x8142c / 0x81434 write the locals' shadow bytes (SF + 4 / 8 / 12) := 00 (lifetime start: this is
     decode_spec_ff's `range_addressable (aview ..) SHADOW_OFF lenp 8` for all three lenp) and 0x81428 / 0x81430 /
     0x81438 zero the three locals; 0x8143c `ld a0,24(s1)` reloads a, 0x81440 `mv a1,s10`;
   - 0x81444 `jal preset_base64_decode` (ra 0x81448): INV_D1.
   NO edge of this range reaches the abort block 0x815f4 or the UBSan trap 0x815fc, and neither inline check reaches
   its report (0x81608 / 0x81614): every branch above is closed by the engine on this file's facts.
   Template (text only): lib/A/FSW_check_no_overread_top.v at a working branch cefc3a4505b (its segM
   pieces ss_S0 / cno_R22 / cno_R52 / cno_GS / cno_vm1 / cno_app_regions / cno_st_lift). Kit lemmas by path.
   rule 24: proves PART of check_no_overread's walk only (the lookup line is lib/B/FSW_check_no_overread.v's header). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YP08.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YCeo.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_ret FSW_rres FSW_frame FSW_strkit FSW_rd FSH_Fn_cno FSH_Fn_alloc
FSW_check_no_overread_tbl FSW_check_no_overread FSW_check_no_overread_inv FSW_check_no_overread_mem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require FSH_Fn_writer YCem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ================= pure arithmetic of the two UBSan guards and the slow paths ================= *)
(* `not rd, rs` is `xori rd, rs, -1`: over 64 bits it is 2 ^ 64 - 1 - t *)
Lemma cno_not64 : forall t, 0 <= t < 2 ^ 64 -> Z.lxor t (2 ^ 64 - 1) = 2 ^ 64 - 1 - t.
Proof.
intros t Ht.
assert (Hl : Z.land t (2 ^ 64 - 1) = t).
{ replace (2 ^ 64 - 1) with (Z.ones 64) by (vm_compute; reflexivity).
  rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
pose proof (Z.add_lxor_2land t (2 ^ 64 - 1)) as H. rewrite Hl in H. lia.
Qed.
(* `andi a2, a0, 7` is the granule offset *)
Lemma cno_land7 : forall x, 0 <= x -> Z.land x 7 = x mod 8.
Proof. intros x Hx. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

(* ================= the states of this span ================= *)
(* the common state at 0x813bc: the boundary's four regions, with s5 on the walk's t atom (10). The n = 0 arm reaches
   it with s5 = a0 = atom 10 (0x813a4 `mv s5,a0`), the memcpy arm with s5 = atom 21 re-seated on atom 10 (both are t). *)
Definition ss_C : sstate :=
  let X := cno_ss 0x813bc 19 18 cno_flag_chunk cno_sl18 in
  mkSS (ss_pc X) (sr_set (ss_regs X) 21%bv (SOff 10 0)) (ss_mem X) (ss_resv X) (ss_facts X).
(* the resume state at 0x813f8, after __asan_memset *)
Definition ss_S : sstate := cno_ss 0x813f8 19 18 cno_flag_chunk cno_sl18.
(* the two regions an inline check needs: the stored byte x (atom 51, writable) and the shadow byte of its granule
   (address atom 53, value atom 54) *)
Definition cno_RX : YP09.region := YP09.mkRegion (Some 51%nat) 0 1 0 1 [].
Definition cno_RSH : YP09.region := YP09.mkRegion (Some 53%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 54 0))].
(* the aliases the engine needs for `add a0,s5,s6; srli a1,a0,3; add a1,a1,s8` (51 = x, 52 = x >> 3, 53 = s8 + 52)
   and, at 0x813bc, for `not s7,s5` (55 = ~t) *)
Definition cno_GC : facts := mkFacts
  ((51%nat, mkAF 4096 (2 ^ 48) 0) :: (52%nat, mkAF 0 (2 ^ 45) 0) ::
   (53%nat, mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 0) :: (54%nat, mkAF 0 7 0) ::
   (55%nat, mkAF (2 ^ 64 - 1 - 2 ^ 47) (2 ^ 64 - 1) 0) ::
   (10%nat, mkAF 4096 (2 ^ 47) 0) :: (22%nat, mkAF 0 PRESET_FILE_MAX_BYTES 0) :: f_atoms (ss_facts ss_C))
  (f_conds (ss_facts ss_C))
  [(SAlu ALU_ADD (SOff 10 0) (SOff 22 0), SOff 51 0);
   (SAlu ALU_SRL (SOff 51 0) (SLit 3), SOff 52 0);
   (SAlu ALU_ADD (SOff 52 0) (SOff 24 0), SOff 53 0);
   (SAlu ALU_XOR (SOff 10 0) (SLit (-1)), SOff 55 0)].
Definition ss_C1 : sstate :=
  set_facts (mkSS (ss_pc ss_C) (ss_regs ss_C) (ss_mem ss_C ++ [cno_RX; cno_RSH]) (ss_resv ss_C) (ss_facts ss_C)) cno_GC.
Definition cno_GS : facts := mkFacts
  ((51%nat, mkAF 4096 (2 ^ 48) 0) :: (52%nat, mkAF 0 (2 ^ 45) 0) ::
   (53%nat, mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 0) :: (54%nat, mkAF 0 7 0) ::
   (21%nat, mkAF 4096 (2 ^ 47) 0) :: (22%nat, mkAF 0 (PRESET_FILE_MAX_BYTES + 17) 0) ::
   (23%nat, mkAF (2 ^ 64 - 1 - 2 ^ 47) (2 ^ 64 - 1) 0) :: f_atoms (ss_facts ss_S))
  (f_conds (ss_facts ss_S))
  [(SAlu ALU_ADD (SOff 21 0) (SOff 22 0), SOff 51 0);
   (SAlu ALU_SRL (SOff 51 0) (SLit 3), SOff 52 0);
   (SAlu ALU_ADD (SOff 52 0) (SOff 24 0), SOff 53 0)].
Definition ss_S1 : sstate :=
  set_facts (mkSS (ss_pc ss_S) (ss_regs ss_S) (ss_mem ss_S ++ [cno_RX; cno_RSH]) (ss_resv ss_S) (ss_facts ss_S)) cno_GS.
(* at 0x813a0 the engine needs only the two atom facts the branches `beqz a0` and `beqz s6` read: t is a live block
   (4096 <= t) and n <= PRESET_FILE_MAX_BYTES *)
Definition cno_GM : facts := mkFacts
  ((10%nat, mkAF 4096 (2 ^ 47) 0) :: (22%nat, mkAF 0 PRESET_FILE_MAX_BYTES 0) :: f_atoms (ss_facts ss_M))
  (f_conds (ss_facts ss_M)) (f_alias (ss_facts ss_M)).
Definition ss_M1 : sstate := set_facts ss_M cno_GM.

(* ================= generic state steps (A's _top.v text) ================= *)
(* a byte the view reads, as a one-byte val_mem, and back *)
Lemma cno_vm1 : forall H (m : word -> option byte) a v,
  aview tfibsegs H m a = Some v -> val_mem tfibsegs (mrestrict H m) a 1 v.
Proof.
intros H m a v Hv k Hk. replace k with 0%nat by lia. rewrite Z.add_0_r.
unfold aview in Hv. destruct (mbyte tfibsegs (mrestrict H m) a) as [b|] eqn:Eb; [|discriminate].
cbn [option_map] in Hv. injection Hv as <-. f_equal.
pose proof (bv_unsigned_in_range 8 b) as Hr. unfold bv_modulus in Hr. cbn in Hr.
rewrite (le_byte_small (bv_unsigned b) 1 0) by (cbn; lia). replace (8 * Z.of_nat 0) with 0 by reflexivity.
rewrite Z.shiftr_0_r. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma cno_av1 : forall H (m : word -> option byte) a v,
  val_mem tfibsegs (mrestrict H m) a 1 v -> 0 <= v < 256 -> aview tfibsegs H m a = Some v.
Proof.
intros H m a v Hv Hr. pose proof (Hv 0%nat ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
rewrite (le_byte_small v 1 0) in H0 by (cbn; lia).
replace (8 * Z.of_nat 0) with 0 in H0 by reflexivity. rewrite Z.shiftr_0_r in H0.
unfold aview. rewrite H0. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. lia.
Qed.
(* regions appended to a state (lib/A/AD25.v:21, which this walk does not load) *)
Lemma cno_app_regions {fx : YK11.FPState} : forall E ss ms rs',
  st_ok tfibsegs E ss ms -> regions_wf rs' = true -> Forall (region_ok tfibsegs E (ms_mem ms)) rs' ->
  pairwise_disjoint E rs' -> (forall r1 r2, In r1 (ss_mem ss) -> In r2 rs' -> extent_disjoint E r1 r2) ->
  st_ok tfibsegs E (mkSS (ss_pc ss) (ss_regs ss) (ss_mem ss ++ rs') (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms rs' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (Hwf & Hok & Hpd) & H9) Hwf' Hok' Hpd' Hx.
unfold st_ok; cbn. repeat (split; [assumption|]). split; [|exact H9]. split; [| split].
- clear -Hwf Hwf'. induction (ss_mem ss) as [|r rs IH]; cbn in *; [exact Hwf'|]. apply andb_prop in Hwf as [Ha Hb].
  rewrite Ha, (IH Hb). reflexivity.
- apply Forall_app. split; assumption.
- apply YP08.pairwise_disjoint_app; assumption.
Qed.

(* the state the span ends in, at the first preset_base64_decode call (both arms of the second inline check reach it
   with THESE registers and THESE regions; only their conds differ, and nothing below reads a cond) *)
Definition ss_D : sstate := Eval vm_compute in
  fst (sym_run_toN tfibsegs cno_tbl FUEL A_preset_base64_decode
         (add_cond ss_S1 (mkAC BC_EQ (SOff 54 0) (SLit 0)))).

(* a frame local whose granule's shadow byte is 00 is addressable: decode_spec_ff's lenp premise *)
Lemma cno_lenp_ra : forall (W : world tfibsegs) m F o,
  F mod 32 = 0 -> 0 <= F -> 0 <= o -> o mod 8 = 0 ->
  aview tfibsegs (w_H W) m (shadow_addr F + o / 8) = Some 0 ->
  range_addressable (aview tfibsegs (w_H W) m) SHADOW_OFF (F + o) 8.
Proof.
intros W m F o Hal HF Ho0 Ho Hav x Hx. exists 0. split; [|left; reflexivity].
replace (shadow_of_addr SHADOW_OFF x) with (shadow_addr F + o / 8); [exact Hav|].
unfold shadow_of_addr, shadow_addr, SHADOW_OFF. Z.div_mod_to_equations. lia.
Qed.

(* the registers INV_D1 reads at the decode call: both arms of the second inline check agree on these (a2 holds the
   slow path's granule offset in one arm and is untouched in the other, and nothing below reads it) *)
Definition cno_D_regs : list (bv 5) := [1; 2; 3; 4; 8; 9; 10; 11; 18; 19; 20; 21; 23; 26; 27]%bv.
Ltac cno_inreg := cbv [cno_D_regs In]; repeat (first [left; reflexivity | right]).
(* the state at the __asan_memset call (both arms of the FIRST inline check reach it with these registers and
   regions) *)
Definition ss_MS : sstate := Eval vm_compute in
  fst (sym_run_toN tfibsegs cno_tbl FUEL PC_memset (add_cond ss_C1 (mkAC BC_EQ (SOff 54 0) (SLit 0)))).

(* ================= the span's own boundaries ================= *)
Section M. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
(* the two runtime contracts this span's calls use (CTX-free S0 forms; the call steps are _mem.v's) *)
Hypothesis AMEMCPY : FSupoisonU.aintrin_realizesU tfibsegs B OCpy PC_memcpy.
Hypothesis AMEMSET : FSupoisonU.aintrin_realizesU tfibsegs B OSet PC_memset.

(* at 0x813bc (ss_C): the three raw blocks are live, t holds d's text (the memcpy arm) or nothing (n = 0), and the
   block's shadow is addressable (cno_call_mal's post, kept by __asan_memcpy) *)
Definition INV_C : cno_inv := fun cx E k ly3 S3 U3 W3 ms3 md3 => exists a b t,
  U3 = c_U cx /\ k = 3 /\ ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) ++ cno_raw cx a b t /\
  FSupoisonU.fs_heads B ly3 S3 U3 /\
  cno_core cx E /\ ew E 10 = w64 t /\ ew E 20 = w64 b /\ ew E 22 = w64 (cno_n cx) /\
  ew E 24 = w64 SHADOW_OFF /\ ew E 25 = w64 (cno_F cx) /\
  ew E 48 = w64 a /\ ew E 49 = w64 b /\ ew E 50 = w64 t /\
  zbytes_at tfibsegs W3 (ms_mem ms3) a (pn_copy (c_db cx) 65) /\
  zbytes_at tfibsegs W3 (ms_mem ms3) b (pn_copy (c_db cx) 66) /\
  zbytes_at tfibsegs W3 (ms_mem ms3) t (c_db cx) /\
  range_addressable (aview tfibsegs (w_H W3) (ms_mem ms3)) SHADOW_OFF t (cno_n cx + 18) /\
  fs_glob tfibsegs W3 (ms_mem ms3) (c_live cx) (c_peak cx) (c_cnt cx) (c_fail cx).

(* at 0x813f8 (ss_S), the return of __asan_memset: t holds d's text, the NUL at t[n] (0x813dc) and the memset's
   sixteen zeros; a0 = t + n + 1, s6 = n + 17, s7 = ~t *)
Definition INV_S : cno_inv := fun cx E k ly3 S3 U3 W3 ms3 md3 => exists a b t,
  U3 = c_U cx /\ k = 3 /\ ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) ++ cno_raw cx a b t /\
  FSupoisonU.fs_heads B ly3 S3 U3 /\
  cno_core cx E /\ ew E 10 = w64 (t + cno_n cx + 1) /\ ew E 20 = w64 b /\ ew E 21 = w64 t /\
  ew E 22 = w64 (cno_n cx + 17) /\ ew E 23 = w64 (2 ^ 64 - 1 - t) /\ ew E 24 = w64 SHADOW_OFF /\
  ew E 25 = w64 (cno_F cx) /\ ew E 48 = w64 a /\ ew E 49 = w64 b /\ ew E 50 = w64 t /\
  zbytes_at tfibsegs W3 (ms_mem ms3) a (pn_copy (c_db cx) 65) /\
  zbytes_at tfibsegs W3 (ms_mem ms3) b (pn_copy (c_db cx) 66) /\
  zbytes_at tfibsegs W3 (ms_mem ms3) t (c_db cx ++ repeat 0 17%nat) /\
  range_addressable (aview tfibsegs (w_H W3) (ms_mem ms3)) SHADOW_OFF t (cno_n cx + 18) /\
  fs_glob tfibsegs W3 (ms_mem ms3) (c_live cx) (c_peak cx) (c_cnt cx) (c_fail cx).

(* ---- the thirteen saved words of a boundary state, as the val_mem facts cno_mframe carries ---- *)
Lemma cno_saved_vm : forall cx E (W : world tfibsegs) m,
  cno_E cx E -> Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W) m) (cno_sp0 cx)) cno_sv_chunks ->
  forall j, (j < 13)%nat ->
  val_mem tfibsegs (mrestrict (w_H W) m) (cno_sp0 cx - 8 * (Z.of_nat j + 1)) 8
    (bv_unsigned (getr (c_regs cx) (nth j cno_saved_regs 0%bv))).
Proof.
intros cx E W m HE HF j Hj.
assert (Hin : In (YP09.mkChunk (- 8 * (Z.of_nat j + 1)) (CVal 8 (SOff (33 + j) 0))) cno_sv_chunks).
{ unfold cno_sv_chunks. apply in_map_iff. exists j. split; [reflexivity|]. apply in_seq. lia. }
pose proof (proj1 (Forall_forall _ _) HF _ Hin) as Hck.
pose proof (val_of_chunk_ok tfibsegs E (mrestrict (w_H W) m) (cno_sp0 cx) (- 8 * (Z.of_nat j + 1)) 8
  (SOff (33 + j) 0) (bv_unsigned (getr (c_regs cx) (nth j cno_saved_regs 0%bv))) Hck) as HV.
replace (cno_sp0 cx + - 8 * (Z.of_nat j + 1)) with (cno_sp0 cx - 8 * (Z.of_nat j + 1)) in HV by lia.
cbn [N.to_nat Pos.to_nat Pos.iter_op] in HV.
apply HV.
- rewrite fsw_SOff0, (proj1 (proj2 HE) j Hj). symmetry. apply Z_to_bv_bv_unsigned.
- change (8 * Z.of_N 8) with 64. apply u64_range.
- cbn. lia.
Qed.

(* ---- the three raw blocks of the walk, read off the journal's AR (the _mem.v twin cno_tblock asks for a call site,
   which the states inside a span have not got: the ra at 0x813bc / 0x813f8 is the previous call's) ---- *)
(* a byte of a live block is no byte of the allocator's statics: a block lies below 0x10000 or at or above
   FS_IMG_END (YCbq's client-image law through FSW_rd.fsw_ablock_off_img), the four cells lie in between *)
Lemma cno_blk_offfp : forall ly S (W : world tfibsegs) mem md p n y,
  AR tfibsegs B ly S W mem md -> In (p, n) (ablocks B ly S) -> p <= y < p + req_size n ->
  ~ inFP FS_PSTAT_FP y.
Proof.
intros ly S W mem md p n y HAR Hin Hy Hfp.
pose proof (cno_pstat_bounds y Hfp) as Hb2.
destruct (fsw_ablock_off_img B ly S W mem md p n HAR Hin) as [Ho | Ho]; unfold FS_IMG_END in Ho; lia.
Qed.
(* the SHADOW byte of a live block's byte is outside cno_zone too: it is in the shadow band, the walk's stack is
   above alloc_ceiling, the fake frame is application memory, and the frame's own sixteen shadow bytes belong to the
   frame's granules, which the block's are not (YCbq.sep_block_frame plus the 16 / 32 alignments) *)
Lemma cno_zone_blksh : forall cx ly S U (W : world tfibsegs) mem md p n i,
  cno_base B cx -> ARU tfibsegs B ly S U W mem md -> In (1, c_fpos cx) (frames S) ->
  ly_F ly = ly_F (c_ly cx) -> In (p, n) (ablocks B ly S) -> 0 <= i < req_size n ->
  ~ cno_zone cx (SHADOW_OFF + (p + i) / 8).
Proof.
intros cx ly S U W mem md p n i Hb HARU Hin EF Hp Hi.
pose proof (cno_nums B cx Hb) as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
pose proof asan_consts as (CA1 & CA2 & CA3 & CA4 & CA5). pose proof cno_stk as FS.
pose proof (ARU_AR tfibsegs B ly S U W mem md HARU) as HAR.
assert (EFa : frame_addr ly 1 (c_fpos cx) = cno_F cx) by (unfold cno_F, frame_addr; rewrite EF; reflexivity).
destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md p n HAR Hp) as (Hal16 & Hp4096 & Hpc & Hpapp & _).
destruct (frames_bounds tfibsegs B LAWS ly S W (unpoison U mem) md 1 (c_fpos cx) HAR Hin)
  as (HF4096 & HFceil & HFapp).
rewrite EFa in HF4096, HFceil, HFapp. change (fs_frame_bytes 1) with 128 in HF4096, HFceil, HFapp.
destruct (al_frames _ _ LAWS ly S W (unpoison U mem) md 1 (c_fpos cx) HAR Hin) as (Hal32 & _ & _ & _).
rewrite EFa in Hal32.
pose proof (sep_block_frame tfibsegs B LAWS ly S W (unpoison U mem) md p n 1 (c_fpos cx) HAR Hp Hin) as Hd.
rewrite EFa in Hd. change (fs_frame_bytes 1) with 128 in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
assert (Hq : 8 * ((p + i) / 8) <= p + i < 8 * ((p + i) / 8) + 8) by (Z.div_mod_to_equations; lia).
assert (HqF : 8 * (cno_F cx / 8) = cno_F cx) by (Z.div_mod_to_equations; lia).
assert (HSFv : cno_SF cx = SHADOW_OFF + cno_F cx / 8) by (unfold cno_SF, shadow_addr; reflexivity).
intros Hz. unfold cno_zone in Hz. rewrite HSFv in Hz.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in Hpapp, HFapp.
destruct Hpapp as (_ & Hpa). destruct HFapp as (_ & HFa).
unfold SHADOW_OFF in Hz. Z.div_mod_to_equations. lia.
Qed.
(* an addressable range stays addressable where the shadow bytes are kept *)
Lemma cno_rad_kept : forall (W W' : world tfibsegs) (m m' : word -> option byte) p n,
  range_addressable (aview tfibsegs (w_H W) m) SHADOW_OFF p n ->
  (forall x, p <= x < p + n ->
     aview tfibsegs (w_H W') m' (SHADOW_OFF + x / 8) = aview tfibsegs (w_H W) m (SHADOW_OFF + x / 8)) ->
  range_addressable (aview tfibsegs (w_H W') m') SHADOW_OFF p n.
Proof.
intros W W' m m' p n Hra Hk x Hx. destruct (Hra x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
unfold shadow_of_addr in *. rewrite (Hk x Hx). exact Hs.
Qed.
Lemma cno_tfacts : forall cx ly S (W : world tfibsegs) mem md a b t,
  cno_base B cx -> AR tfibsegs B ly S W (unpoison (c_U cx) mem) md ->
  ablocks B ly S = ablocks B (c_ly cx) (c_S cx) ++ cno_raw cx a b t ->
  req_size (cno_n cx + 18) = cno_n cx + 18 /\
  In (t, cno_n cx + 18) (ablocks B ly S) /\ ~ In (t, cno_n cx + 18) (ablocks B (c_ly cx) (c_S cx)) /\
  4096 <= t /\ t + (cno_n cx + 18) <= alloc_ceiling /\ in_app t (cno_n cx + 18) /\
  (forall y, t <= y < t + (cno_n cx + 18) ->
     apresent (w_H W) (unpoison (c_U cx) mem) y /\ ~ aowned B ly S y) /\
  In (a, cno_n cx + 18) (ablocks B ly S) /\ In (b, cno_n cx + 18) (ablocks B ly S) /\
  4096 <= a /\ a + (cno_n cx + 18) <= alloc_ceiling /\
  4096 <= b /\ b + (cno_n cx + 18) <= alloc_ceiling /\
  (a + (cno_n cx + 18) <= t \/ t + (cno_n cx + 18) <= a) /\
  (b + (cno_n cx + 18) <= t \/ t + (cno_n cx + 18) <= b) /\
  (forall p m, In (p, m) (ablocks B (c_ly cx) (c_S cx)) ->
     In (p, m) (ablocks B ly S) /\ (p + req_size m <= t \/ t + (cno_n cx + 18) <= p)).
Proof.
intros cx ly S W mem md a b t Hb HAR Hab.
assert (Hn0 : 0 <= cno_n cx) by (unfold cno_n; lia).
assert (Hreq : req_size (cno_n cx + 18) = cno_n cx + 18)
  by (unfold req_size; destruct (cno_n cx + 18 =? 0) eqn:Ez; [apply Z.eqb_eq in Ez; lia | reflexivity]).
assert (HtIn : In (t, cno_n cx + 18) (ablocks B ly S))
  by (rewrite Hab; apply in_or_app; right; right; right; left; reflexivity).
assert (HaIn : In (a, cno_n cx + 18) (ablocks B ly S))
  by (rewrite Hab; apply in_or_app; right; left; reflexivity).
assert (HbIn : In (b, cno_n cx + 18) (ablocks B ly S))
  by (rewrite Hab; apply in_or_app; right; right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly S W (unpoison (c_U cx) mem) md t (cno_n cx + 18) HAR HtIn)
  as (_ & Ht4096 & Htc & Htapp & Htp & _).
destruct (al_blocks _ _ LAWS ly S W (unpoison (c_U cx) mem) md a (cno_n cx + 18) HAR HaIn)
  as (_ & Ha4096 & Hac & _).
destruct (al_blocks _ _ LAWS ly S W (unpoison (c_U cx) mem) md b (cno_n cx + 18) HAR HbIn)
  as (_ & Hb4096 & Hbc & _).
rewrite Hreq in Htc, Htapp, Htp, Hac, Hbc.
assert (Hat : a + (cno_n cx + 18) <= t \/ t + (cno_n cx + 18) <= a).
{ pose proof (sep_blocks_pos tfibsegs B LAWS ly S W (unpoison (c_U cx) mem) md
    (a, cno_n cx + 18) (t, cno_n cx + 18) (ablocks B (c_ly cx) (c_S cx)) [(b, cno_n cx + 18)] [] HAR
    ltac:(rewrite Hab; cbn [app cno_raw]; reflexivity)) as Hd.
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. rewrite Hreq in Hd. lia. }
assert (Hbt : b + (cno_n cx + 18) <= t \/ t + (cno_n cx + 18) <= b).
{ pose proof (sep_blocks_pos tfibsegs B LAWS ly S W (unpoison (c_U cx) mem) md
    (b, cno_n cx + 18) (t, cno_n cx + 18) (ablocks B (c_ly cx) (c_S cx) ++ [(a, cno_n cx + 18)]) [] [] HAR
    ltac:(rewrite Hab; cbn [app cno_raw]; rewrite <- app_assoc; cbn [app]; reflexivity)) as Hd.
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. rewrite Hreq in Hd. lia. }
assert (Hd0 : forall p m, In (p, m) (ablocks B (c_ly cx) (c_S cx)) ->
  In (p, m) (ablocks B ly S) /\ (p + req_size m <= t \/ t + (cno_n cx + 18) <= p)).
{ intros p m Hp. split; [rewrite Hab; apply in_or_app; left; exact Hp|].
  apply in_split in Hp as (l1 & l2 & Ebq).
  pose proof (sep_blocks_pos tfibsegs B LAWS ly S W (unpoison (c_U cx) mem) md
    (p, m) (t, cno_n cx + 18) l1 (l2 ++ [(a, cno_n cx + 18); (b, cno_n cx + 18)]) [] HAR
    ltac:(rewrite Hab, Ebq; cbn [app cno_raw]; repeat rewrite <- app_assoc; cbn [app]; reflexivity)) as Hd.
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. rewrite Hreq in Hd. lia. }
split; [exact Hreq|]. split; [exact HtIn|].
split; [intros Hin; destruct (Hd0 t (cno_n cx + 18) Hin) as (_ & Hdd); rewrite Hreq in Hdd; lia|].
split; [exact Ht4096|]. split; [exact Htc|]. split; [exact Htapp|]. split; [exact Htp|].
split; [exact HaIn|]. split; [exact HbIn|].
split; [exact Ha4096|]. split; [lia|]. split; [exact Hb4096|]. split; [lia|].
split; [exact Hat|]. split; [exact Hbt | exact Hd0].
Qed.

(* ---- the write window of a run from a boundary state with the inline check's two regions, and the bytes such a
   run keeps: cno_zone plus the single stored byte x ---- *)
Lemma awr_ok_app : forall E l1 l2 STK sp0 FP bl0 blc ly own fr0,
  awr_ok tfibsegs B E l1 STK sp0 FP bl0 blc ly own fr0 ->
  awr_ok tfibsegs B E l2 STK sp0 FP bl0 blc ly own fr0 ->
  awr_ok tfibsegs B E (l1 ++ l2) STK sp0 FP bl0 blc ly own fr0.
Proof.
intros E l1 l2 STK sp0 FP bl0 blc ly own fr0 H1 H2 x (r & Hin & Hw).
apply in_app_or in Hin. destruct Hin as [Hin | Hin]; [apply H1 | apply H2]; exists r; split; assumption.
Qed.
Lemma cno_wr_zoneX : forall cx E r csF cssl x a,
  bv_unsigned (ew E 8) = cno_sp0 cx -> bv_unsigned (ew E 9) = cno_sp1 cx ->
  bv_unsigned (ew E 19) = cno_F cx -> bv_unsigned (ew E 18) = cno_SF cx -> bv_unsigned (ew E 51) = x ->
  in_wrange E (ss_mem (cno_ss r 19 18 csF cssl) ++ [cno_RX; cno_RSH]) a -> cno_zone cx a \/ a = x.
Proof.
intros cx E r csF cssl x a E8 E9 E19 E18 E51 (rg & Hin & Hw).
unfold cno_ss, fss_ret_s0_args, fss_ret_s0_regs, fs_ret_s0_region, cno_fr_region, cno_sh_region, cno_sl_region,
  cno_RX, cno_RSH in Hin.
cbn [ss_mem app] in Hin. unfold cno_zone.
destruct Hin as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
  first [rewrite E8 in Hw | rewrite E19 in Hw | rewrite E18 in Hw | rewrite E9 in Hw | rewrite E51 in Hw | idtac];
  first [left; lia | right; lia].
Qed.
Lemma cno_keepX : forall cx E r csF cssl ly S U (W : world tfibsegs) mem md x (m m' : word -> option byte),
  cno_base B cx -> ARU tfibsegs B ly S U W mem md -> In (1, c_fpos cx) (frames S) ->
  ly_F ly = ly_F (c_ly cx) ->
  bv_unsigned (ew E 8) = cno_sp0 cx -> bv_unsigned (ew E 9) = cno_sp1 cx ->
  bv_unsigned (ew E 19) = cno_F cx -> bv_unsigned (ew E 18) = cno_SF cx -> bv_unsigned (ew E 51) = x ->
  frame_of E (ss_mem (cno_ss r 19 18 csF cssl) ++ [cno_RX; cno_RSH]) m m' ->
  (forall a, inFP FS_PSTAT_FP a -> a <> x -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) /\
  (forall p n i, In (p, n) (ablocks B ly S) -> 0 <= i < req_size n -> p + i <> x ->
     m' (Z_to_bv 64 (p + i)) = m (Z_to_bv 64 (p + i))).
Proof.
intros cx E r csF cssl ly S U W mem md x m m' Hb HARU Hin EF E8 E9 E19 E18 E51 HF.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (ARU_AR tfibsegs B ly S U W mem md HARU) as HAR.
split.
- intros a Ha Hax. apply HF. assert (Ha64 : 0 <= a < 2 ^ 64).
  { pose proof (fs_segs_low a (cno_pstat_img a Ha)). unfold kLowMemEnd in *. lia. }
  rewrite (wz a Ha64). intros Hw.
  destruct (cno_wr_zoneX cx E r csF cssl x a E8 E9 E19 E18 E51 Hw) as [Hz | Hz]; [|exact (Hax Hz)].
  exact (cno_zone_ledger B cx ly S U W mem md a Hb HARU Hin EF Ha Hz).
- intros p n i Hp Hi Hpx. apply HF.
  destruct (fsw_ablock_low B ly S W (unpoison U mem) md p n HAR Hp) as (L1 & L2 & L3).
  rewrite (wz (p + i) ltac:(lia)). intros Hw.
  destruct (cno_wr_zoneX cx E r csF cssl x (p + i) E8 E9 E19 E18 E51 Hw) as [Hz | Hz]; [|exact (Hpx Hz)].
  exact (cno_zone_blk B cx ly S U W mem md p n i Hb HARU Hin EF Hp Hi Hz).
Qed.

(* ---- the walk's byte windows across a run: one byte at a time, then a zero appended, then concatenation ---- *)
Lemma cno_nth_rep0 : forall n i, nth i (repeat 0 n) 0 = 0.
Proof. induction n as [|n IH]; intros i; destruct i as [|i]; cbn; try reflexivity. apply IH. Qed.
Lemma cno_zb_kept1 : forall (W : world tfibsegs) (m m' : word -> option byte) x v,
  val_mem tfibsegs (mrestrict (w_H W) m) x 1 v -> 0 <= v < 256 ->
  m' (Z_to_bv 64 x) = m (Z_to_bv 64 x) -> val_mem tfibsegs (mrestrict (w_H W) m') x 1 v.
Proof.
intros W m m' x v Hv Hr Hk. apply cno_vm1.
rewrite (aview_at tfibsegs (w_H W) m' m x Hk). apply cno_av1; assumption.
Qed.
Lemma cno_zb_app : forall (W : world tfibsegs) (m : word -> option byte) p (l1 l2 : list Z),
  zbytes_at tfibsegs W m p l1 -> zbytes_at tfibsegs W m (p + Z.of_nat (length l1)) l2 ->
  zbytes_at tfibsegs W m p (l1 ++ l2).
Proof.
intros W m p l1 l2 H1 H2 j Hj. rewrite length_app in Hj.
destruct (Nat.lt_ge_cases j (length l1)) as [Hlt | Hge].
- rewrite app_nth1 by exact Hlt. exact (H1 j Hlt).
- rewrite app_nth2 by exact Hge.
  destruct (H2 (j - length l1)%nat ltac:(lia)) as (Hv & Hr). split; [|exact Hr].
  replace (p + Z.of_nat j) with (p + Z.of_nat (length l1) + Z.of_nat (j - length l1)) by lia. exact Hv.
Qed.
Lemma cno_zb_ext0 : forall (W : world tfibsegs) (m m' : word -> option byte) p (l : list Z) k,
  zbytes_at tfibsegs W m p l -> Z.of_nat (length l) = k ->
  (forall j, 0 <= j < k -> m' (Z_to_bv 64 (p + j)) = m (Z_to_bv 64 (p + j))) ->
  val_mem tfibsegs (mrestrict (w_H W) m') (p + k) 1 0 ->
  zbytes_at tfibsegs W m' p (l ++ [0]).
Proof.
intros W m m' p l k Hz Hk Hkeep Hlast j Hj. rewrite length_app in Hj. cbn [length] in Hj.
destruct (Nat.lt_ge_cases j (length l)) as [Hlt | Hge].
- rewrite app_nth1 by exact Hlt. destruct (Hz j Hlt) as (Hv & Hr). split; [|exact Hr].
  exact (cno_zb_kept1 W m m' (p + Z.of_nat j) (nth j l 0) Hv Hr (Hkeep (Z.of_nat j) ltac:(lia))).
- assert (Ej : j = length l) by lia. subst j. rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth].
  split; [rewrite Hk; exact Hlast | lia].
Qed.
Lemma cno_zb_kept : forall (W : world tfibsegs) (m m' : word -> option byte) p (l : list Z),
  zbytes_at tfibsegs W m p l ->
  (forall j, 0 <= j < Z.of_nat (length l) -> m' (Z_to_bv 64 (p + j)) = m (Z_to_bv 64 (p + j))) ->
  zbytes_at tfibsegs W m' p l.
Proof.
intros W m m' p l Hz Hkeep j Hj. destruct (Hz j Hj) as (Hv & Hr). split; [|exact Hr].
exact (cno_zb_kept1 W m m' (p + Z.of_nat j) (nth j l 0) Hv Hr (Hkeep (Z.of_nat j) ltac:(lia))).
Qed.

(* ---- INV_D1 read off the span's last state (ss_D's registers and regions): both arms of the second inline check
   end here, so this is proved once ---- *)
Lemma cno_segM_D1 : forall cx E ly S (W : world tfibsegs) ms md a b t ssF,
  cno_base B cx -> cno_E cx E ->
  cno_J B cx 3 ly S W (unpoison (c_U cx) (ms_mem ms)) md ->
  ARU tfibsegs B ly S (c_U cx) W (ms_mem ms) md -> FSupoisonU.fs_heads B ly S (c_U cx) ->
  ablocks B ly S = ablocks B (c_ly cx) (c_S cx) ++ cno_raw cx a b t ->
  cno_core cx E -> ew E 20 = w64 b -> ew E 21 = w64 t -> ew E 25 = w64 (cno_F cx) -> ew E 48 = w64 a ->
  zbytes_at tfibsegs W (ms_mem ms) a (pn_copy (c_db cx) 65) ->
  zbytes_at tfibsegs W (ms_mem ms) b (pn_copy (c_db cx) 66) ->
  zbytes_at tfibsegs W (ms_mem ms) t (c_db cx ++ repeat 0 18%nat) ->
  fs_glob tfibsegs W (ms_mem ms) (c_live cx) (c_peak cx) (c_cnt cx) (c_fail cx) ->
  ss_pc ssF = A_preset_base64_decode ->
  (forall r : bv 5, In r cno_D_regs -> sr_get (ss_regs ssF) r = sr_get (ss_regs ss_D) r) ->
  ss_mem ssF = ss_mem ss_D ->
  st_ok tfibsegs E ssF (restrict (w_H W) ms) ->
  INV_D1 B cx 3 ly S (c_U cx) W (ms_regs ms) (ms_mem ms) md.
Proof.
intros cx E ly S W ms md a b t ssF Hb HE HJ HARU Hh Hab Hcore E20 E21 E25 E48 Hza Hzb Hzt Hg Hpc Hrg Hmm HSF.
pose proof (cno_nums B cx Hb) as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
pose proof asan_consts as (CA1 & CA2 & CA3 & CA4 & CA5). pose proof cno_stk as FS.
destruct Hcore as (C2 & C8 & C9 & C18 & C19 & C3 & C4).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _).
assert (Hin : In (1, c_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (EF : ly_F ly = ly_F (c_ly cx)) by (destruct Hly as (_ & _ & _ & _ & _ & X & _); exact X).
assert (EFa : frame_addr ly 1 (c_fpos cx) = cno_F cx) by (unfold cno_F, frame_addr; rewrite EF; reflexivity).
destruct (frames_bounds tfibsegs B LAWS ly S W (unpoison (c_U cx) (ms_mem ms)) md 1 (c_fpos cx) HAR Hin)
  as (HF4096 & HFceil & HFapp).
rewrite EFa in HF4096, HFceil, HFapp. change (fs_frame_bytes 1) with 128 in HF4096, HFceil, HFapp.
destruct (al_frames _ _ LAWS ly S W (unpoison (c_U cx) (ms_mem ms)) md 1 (c_fpos cx) HAR Hin) as (Hal32 & _ & _ & _).
rewrite EFa in Hal32.
assert (HF64 : 0 <= cno_F cx < 2 ^ 64) by (unfold in_app, kLowShadowBeg, ASAN_CEIL in HFapp; lia).
pose proof (shadow_addr_bounds (cno_F cx) ltac:(unfold kHighMemEnd; lia)) as (Hs1 & Hs2).
assert (HSF64 : 0 <= cno_SF cx < 2 ^ 64) by (unfold cno_SF, kLowMemEnd, kHighShadowEnd in *; lia).
assert (HaIn : In (a, cno_n cx + 18) (ablocks B ly S)) by (rewrite Hab; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly S W (unpoison (c_U cx) (ms_mem ms)) md a (cno_n cx + 18) HAR HaIn)
  as (_ & Ha4096 & Hac & _).
pose proof (req_size_pos (cno_n cx + 18) ltac:(unfold cno_n; lia)) as (Hrq1 & Hrq2).
assert (Ha64 : 0 <= a < 2 ^ 64) by lia.
(* the unsigned readings of the boundary atoms *)
assert (U8 : bv_unsigned (ew E 8) = cno_sp0 cx) by (rewrite C8; unfold w64; apply wz; lia).
assert (U9 : bv_unsigned (ew E 9) = cno_sp1 cx) by (rewrite C9; unfold w64; apply wz; lia).
assert (U19 : bv_unsigned (ew E 19) = cno_F cx) by (rewrite C19; unfold w64; apply wz; lia).
assert (U18 : bv_unsigned (ew E 18) = cno_SF cx) by (rewrite C18; unfold w64; apply wz; lia).
(* the registers at the call *)
assert (R1 : getr (ms_regs ms) 1 = w64 0x81448)
  by (apply (fsw_reg_lit (w_H W) E ssF ms 1%bv 0x81448 HSF);
      [rewrite (Hrg 1%bv ltac:(cno_inreg)); vm_compute; reflexivity | lia]).
assert (R10 : getr (ms_regs ms) 10 = w64 a)
  by (rewrite (cno_reg (w_H W) E ssF ms 10%bv 48 HSF
       ltac:(rewrite (Hrg 10%bv ltac:(cno_inreg)); vm_compute; reflexivity)); exact E48).
assert (R11 : getr (ms_regs ms) 11 = w64 (cno_F cx + 32))
  by (apply (cno_reg_off (w_H W) E ssF ms 11%bv 19 32 (cno_F cx) HSF
       ltac:(rewrite (Hrg 11%bv ltac:(cno_inreg)); vm_compute; reflexivity) C19 ltac:(lia) ltac:(lia))).
assert (R20 : getr (ms_regs ms) 20 = w64 b)
  by (rewrite (cno_reg (w_H W) E ssF ms 20%bv 20 HSF
       ltac:(rewrite (Hrg 20%bv ltac:(cno_inreg)); vm_compute; reflexivity)); exact E20).
assert (R21 : getr (ms_regs ms) 21 = w64 t)
  by (rewrite (cno_reg (w_H W) E ssF ms 21%bv 21 HSF
       ltac:(rewrite (Hrg 21%bv ltac:(cno_inreg)); vm_compute; reflexivity)); exact E21).
assert (R23 : getr (ms_regs ms) 23 = w64 (cno_F cx + 64))
  by (apply (cno_reg_off (w_H W) E ssF ms 23%bv 19 64 (cno_F cx) HSF
       ltac:(rewrite (Hrg 23%bv ltac:(cno_inreg)); vm_compute; reflexivity) C19 ltac:(lia) ltac:(lia))).
assert (R26 : getr (ms_regs ms) 26 = w64 (cno_F cx + 32))
  by (apply (cno_reg_off (w_H W) E ssF ms 26%bv 19 32 (cno_F cx) HSF
       ltac:(rewrite (Hrg 26%bv ltac:(cno_inreg)); vm_compute; reflexivity) C19 ltac:(lia) ltac:(lia))).
assert (R27 : getr (ms_regs ms) 27 = w64 (cno_F cx + 96))
  by (apply (cno_reg_off (w_H W) E ssF ms 27%bv 19 96 (cno_F cx) HSF
       ltac:(rewrite (Hrg 27%bv ltac:(cno_inreg)); vm_compute; reflexivity) C19 ltac:(lia) ltac:(lia))).
assert (R2 : getr (ms_regs ms) 2 = w64 (cno_sp1 cx))
  by (rewrite (cno_reg (w_H W) E ssF ms 2%bv 2 HSF
       ltac:(rewrite (Hrg 2%bv ltac:(cno_inreg)); vm_compute; reflexivity)); exact C2).
assert (R8 : getr (ms_regs ms) 8 = w64 (cno_sp0 cx))
  by (rewrite (cno_reg (w_H W) E ssF ms 8%bv 8 HSF
       ltac:(rewrite (Hrg 8%bv ltac:(cno_inreg)); vm_compute; reflexivity)); exact C8).
assert (R9 : getr (ms_regs ms) 9 = w64 (cno_sp1 cx))
  by (rewrite (cno_reg (w_H W) E ssF ms 9%bv 9 HSF
       ltac:(rewrite (Hrg 9%bv ltac:(cno_inreg)); vm_compute; reflexivity)); exact C9).
assert (R18 : getr (ms_regs ms) 18 = w64 (cno_SF cx))
  by (rewrite (cno_reg (w_H W) E ssF ms 18%bv 18 HSF
       ltac:(rewrite (Hrg 18%bv ltac:(cno_inreg)); vm_compute; reflexivity)); exact C18).
assert (R19 : getr (ms_regs ms) 19 = w64 (cno_F cx))
  by (rewrite (cno_reg (w_H W) E ssF ms 19%bv 19 HSF
       ltac:(rewrite (Hrg 19%bv ltac:(cno_inreg)); vm_compute; reflexivity)); exact C19).
assert (R3 : getr (ms_regs ms) 3 = getr (c_regs cx) 3)
  by (rewrite (cno_reg (w_H W) E ssF ms 3%bv 3 HSF
       ltac:(rewrite (Hrg 3%bv ltac:(cno_inreg)); vm_compute; reflexivity)); exact C3).
assert (R4 : getr (ms_regs ms) 4 = getr (c_regs cx) 4)
  by (rewrite (cno_reg (w_H W) E ssF ms 4%bv 4 HSF
       ltac:(rewrite (Hrg 4%bv ltac:(cno_inreg)); vm_compute; reflexivity)); exact C4).
(* the saved words *)
destruct (cno_saved_of_st cx E ssF W ms HE U8 HSF ltac:(rewrite Hmm; vm_compute; reflexivity))
  as (_ & _ & Hsvall).
pose proof (cno_saved_vm cx E W (ms_mem ms) HE (Hsvall E ltac:(intros; reflexivity))) as Hsv.
(* the chunks of the frame, its shadow and the slots *)
set (rF := nth 1 (ss_mem ss_D) (YP09.mkRegion None 0 0 0 0 [])).
set (rS := nth 2 (ss_mem ss_D) (YP09.mkRegion None 0 0 0 0 [])).
set (rL := nth 3 (ss_mem ss_D) (YP09.mkRegion None 0 0 0 0 [])).
assert (HrF : nth_error (ss_mem ssF) 1 = Some rF) by (rewrite Hmm; vm_compute; reflexivity).
assert (HrS : nth_error (ss_mem ssF) 2 = Some rS) by (rewrite Hmm; vm_compute; reflexivity).
assert (HrL : nth_error (ss_mem ssF) 3 = Some rL) by (rewrite Hmm; vm_compute; reflexivity).
assert (HcFL : YP09.chunk_ok tfibsegs E (mrestrict (w_H W) (ms_mem ms)) (bv_unsigned (ew E 19))
  (YP09.mkChunk 120 (CVal 8 (SOff 46 0))))
  by (apply (cno_chunk_at E ssF (w_H W) ms 1 rF 19 (YP09.mkChunk 120 (CVal 8 (SOff 46 0))) HSF HrF
       ltac:(vm_compute; reflexivity) ltac:(vm_compute; tauto))).
assert (Hc32 : YP09.chunk_ok tfibsegs E (mrestrict (w_H W) (ms_mem ms)) (bv_unsigned (ew E 19))
  (YP09.mkChunk 32 (CVal 8 (SLit 0))))
  by (apply (cno_chunk_at E ssF (w_H W) ms 1 rF 19 (YP09.mkChunk 32 (CVal 8 (SLit 0))) HSF HrF
       ltac:(vm_compute; reflexivity) ltac:(vm_compute; tauto))).
assert (Hc64 : YP09.chunk_ok tfibsegs E (mrestrict (w_H W) (ms_mem ms)) (bv_unsigned (ew E 19))
  (YP09.mkChunk 64 (CVal 8 (SLit 0))))
  by (apply (cno_chunk_at E ssF (w_H W) ms 1 rF 19 (YP09.mkChunk 64 (CVal 8 (SLit 0))) HSF HrF
       ltac:(vm_compute; reflexivity) ltac:(vm_compute; tauto))).
assert (Hc96 : YP09.chunk_ok tfibsegs E (mrestrict (w_H W) (ms_mem ms)) (bv_unsigned (ew E 19))
  (YP09.mkChunk 96 (CVal 8 (SLit 0))))
  by (apply (cno_chunk_at E ssF (w_H W) ms 1 rF 19 (YP09.mkChunk 96 (CVal 8 (SLit 0))) HSF HrF
       ltac:(vm_compute; reflexivity) ltac:(vm_compute; tauto))).
assert (Hs4 : YP09.chunk_ok tfibsegs E (mrestrict (w_H W) (ms_mem ms)) (bv_unsigned (ew E 18))
  (YP09.mkChunk 4 (CVal 1 (SLit 0))))
  by (apply (cno_chunk_at E ssF (w_H W) ms 2 rS 18 (YP09.mkChunk 4 (CVal 1 (SLit 0))) HSF HrS
       ltac:(vm_compute; reflexivity) ltac:(vm_compute; tauto))).
assert (Hs8 : YP09.chunk_ok tfibsegs E (mrestrict (w_H W) (ms_mem ms)) (bv_unsigned (ew E 18))
  (YP09.mkChunk 8 (CVal 1 (SLit 0))))
  by (apply (cno_chunk_at E ssF (w_H W) ms 2 rS 18 (YP09.mkChunk 8 (CVal 1 (SLit 0))) HSF HrS
       ltac:(vm_compute; reflexivity) ltac:(vm_compute; tauto))).
assert (Hs12 : YP09.chunk_ok tfibsegs E (mrestrict (w_H W) (ms_mem ms)) (bv_unsigned (ew E 18))
  (YP09.mkChunk 12 (CVal 1 (SLit 0))))
  by (apply (cno_chunk_at E ssF (w_H W) ms 2 rS 18 (YP09.mkChunk 12 (CVal 1 (SLit 0))) HSF HrS
       ltac:(vm_compute; reflexivity) ltac:(vm_compute; tauto))).
assert (Hl16 : YP09.chunk_ok tfibsegs E (mrestrict (w_H W) (ms_mem ms)) (bv_unsigned (ew E 9))
  (YP09.mkChunk 16 (CVal 8 (SOff 25 0))))
  by (apply (cno_chunk_at E ssF (w_H W) ms 3 rL 9 (YP09.mkChunk 16 (CVal 8 (SOff 25 0))) HSF HrL
       ltac:(vm_compute; reflexivity) ltac:(vm_compute; tauto))).
assert (Hl24 : YP09.chunk_ok tfibsegs E (mrestrict (w_H W) (ms_mem ms)) (bv_unsigned (ew E 9))
  (YP09.mkChunk 24 (CVal 8 (SOff 48 0))))
  by (apply (cno_chunk_at E ssF (w_H W) ms 3 rL 9 (YP09.mkChunk 24 (CVal 8 (SOff 48 0))) HSF HrL
       ltac:(vm_compute; reflexivity) ltac:(vm_compute; tauto))).
rewrite U19 in HcFL, Hc32, Hc64, Hc96. rewrite U18 in Hs4, Hs8, Hs12. rewrite U9 in Hl16, Hl24.
(* the chunks as val_mem / aview facts *)
pose proof HE as (_ & _ & HE46 & _).
assert (VFL : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (cno_F cx + 120) 8
  (bv_unsigned (w64 (cno_FL cx)))).
{ exact (val_of_chunk_ok tfibsegs E _ _ 120 8 (SOff 46 0) _ HcFL
    ltac:(rewrite fsw_SOff0, HE46; symmetry; apply Z_to_bv_bv_unsigned)
    ltac:(change (8 * Z.of_N 8) with 64; apply u64_range) ltac:(cbn; lia)). }
assert (V16 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (cno_sp1 cx + 16) 8 (cno_F cx)).
{ exact (val_of_chunk_ok tfibsegs E _ _ 16 8 (SOff 25 0) _ Hl16 ltac:(rewrite fsw_SOff0; exact E25)
    ltac:(change (8 * Z.of_N 8) with 64; lia) ltac:(cbn; lia)). }
assert (V24 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (cno_sp1 cx + 24) 8 a).
{ exact (val_of_chunk_ok tfibsegs E _ _ 24 8 (SOff 48 0) _ Hl24 ltac:(rewrite fsw_SOff0; exact E48)
    ltac:(change (8 * Z.of_N 8) with 64; lia) ltac:(cbn; lia)). }
assert (V32 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (cno_F cx + 32) 8 0)
  by (exact (val_of_chunk_ok tfibsegs E _ _ 32 8 (SLit 0) 0 Hc32 ltac:(reflexivity)
       ltac:(change (8 * Z.of_N 8) with 64; lia) ltac:(cbn; lia))).
assert (V64 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (cno_F cx + 64) 8 0)
  by (exact (val_of_chunk_ok tfibsegs E _ _ 64 8 (SLit 0) 0 Hc64 ltac:(reflexivity)
       ltac:(change (8 * Z.of_N 8) with 64; lia) ltac:(cbn; lia))).
assert (V96 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (cno_F cx + 96) 8 0)
  by (exact (val_of_chunk_ok tfibsegs E _ _ 96 8 (SLit 0) 0 Hc96 ltac:(reflexivity)
       ltac:(change (8 * Z.of_N 8) with 64; lia) ltac:(cbn; lia))).
assert (A4 : aview tfibsegs (w_H W) (ms_mem ms) (cno_SF cx + 4) = Some 0).
{ apply cno_av1; [|lia].
  exact (val_of_chunk_ok tfibsegs E _ _ 4 1 (SLit 0) 0 Hs4 ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)). }
assert (A8 : aview tfibsegs (w_H W) (ms_mem ms) (cno_SF cx + 8) = Some 0).
{ apply cno_av1; [|lia].
  exact (val_of_chunk_ok tfibsegs E _ _ 8 1 (SLit 0) 0 Hs8 ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)). }
assert (A12 : aview tfibsegs (w_H W) (ms_mem ms) (cno_SF cx + 12) = Some 0).
{ apply cno_av1; [|lia].
  exact (val_of_chunk_ok tfibsegs E _ _ 12 1 (SLit 0) 0 Hs12 ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)). }
(* the three lenp granules are addressable *)
assert (RA32 : range_addressable (aview tfibsegs (w_H W) (ms_mem ms)) SHADOW_OFF (cno_F cx + 32) 8)
  by (apply (cno_lenp_ra W (ms_mem ms) (cno_F cx) 32 Hal32 ltac:(lia) ltac:(lia) ltac:(reflexivity));
      unfold cno_SF in A4; change (32 / 8) with 4; exact A4).
assert (RA64 : range_addressable (aview tfibsegs (w_H W) (ms_mem ms)) SHADOW_OFF (cno_F cx + 64) 8)
  by (apply (cno_lenp_ra W (ms_mem ms) (cno_F cx) 64 Hal32 ltac:(lia) ltac:(lia) ltac:(reflexivity));
      unfold cno_SF in A8; change (64 / 8) with 8; exact A8).
assert (RA96 : range_addressable (aview tfibsegs (w_H W) (ms_mem ms)) SHADOW_OFF (cno_F cx + 96) 8)
  by (apply (cno_lenp_ra W (ms_mem ms) (cno_F cx) 96 Hal32 ltac:(lia) ltac:(lia) ltac:(reflexivity));
      unfold cno_SF in A12; change (96 / 8) with 12; exact A12).
(* INV_D1 *)
exists a, b, t. split; [reflexivity|]. split; [reflexivity|].
split.
{ split; [exact HJ|]. split; [exact HARU|]. split; [exact Hh|].
  split; [exact R2|]. split; [exact R8|]. split; [exact R9|]. split; [exact R18|]. split; [exact R19|].
  split; [exact R3|]. split; [exact R4|]. split; [exact Hsv|]. split; [exact VFL|]. split; [exact V16 | exact V24]. }
split; [exact Hab|]. split; [exact R1|]. split; [exact R10|]. split; [exact R11|].
split; [exact R20|]. split; [exact R21|]. split; [exact R23|]. split; [exact R26|]. split; [exact R27|].
split; [exact Hza|]. split; [exact Hzb|]. split; [exact Hzt|].
split; [exact V32|]. split; [exact V64|]. split; [exact V96|].
split; [exact RA32|]. split; [exact RA64|]. split; [exact RA96 | exact Hg].
Qed.

(* ---- 0x813f8 -> 0x81444: U3, the slot 0x10 (0x813fc), the second inline check (both arms), the lifetime-start
   stores and the three zeroed locals ---- *)
Lemma cno_seg_M3 : cno_at B A_preset_base64_decode (INV_D1 B) -> cno_from B ss_S INV_S.
Proof.
intros HD1 cx E k ly3 S3 U3 W3 ms3 md3 Hb HE HJ HARU HINV HS.
destruct HINV as (a & b & t & -> & -> & Hab & Hh & Hcore & E10 & E20 & E21 & E22 & E23 & E24 & E25 & E48 & E49 & E50
  & Hza & Hzb & Hzt & Hrad & Hg).
pose proof (cno_nums B cx Hb) as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
pose proof asan_consts as (CA1 & CA2 & CA3 & CA4 & CA5). pose proof cno_stk as FS.
pose proof Hb as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HnM & _).
unfold PRESET_FILE_MAX_BYTES in HnM.
assert (Hn0 : 0 <= cno_n cx) by (unfold cno_n; lia).
pose proof Hcore as (C2 & C8 & C9 & C18 & C19 & C3 & C4).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _).
assert (Hin : In (1, c_fpos cx) (frames S3)) by (rewrite Hfrs; left; reflexivity).
assert (EF : ly_F ly3 = ly_F (c_ly cx)) by (destruct Hly as (_ & _ & _ & _ & _ & X & _); exact X).
assert (EFa : frame_addr ly3 1 (c_fpos cx) = cno_F cx) by (unfold cno_F, frame_addr; rewrite EF; reflexivity).
destruct (frames_bounds tfibsegs B LAWS ly3 S3 W3 (unpoison (c_U cx) (ms_mem ms3)) md3 1 (c_fpos cx) HAR Hin)
  as (HF4096 & HFceil & HFapp).
rewrite EFa in HF4096, HFceil, HFapp. change (fs_frame_bytes 1) with 128 in HF4096, HFceil, HFapp.
destruct (al_frames _ _ LAWS ly3 S3 W3 (unpoison (c_U cx) (ms_mem ms3)) md3 1 (c_fpos cx) HAR Hin)
  as (Hal32 & _ & _ & _).
rewrite EFa in Hal32.
assert (HF64 : 0 <= cno_F cx < 2 ^ 64) by (unfold in_app, kLowShadowBeg, ASAN_CEIL in HFapp; lia).
pose proof (shadow_addr_bounds (cno_F cx) ltac:(unfold kHighMemEnd; lia)) as (Hs1 & Hs2).
unfold kLowMemEnd, kHighShadowEnd in Hs1, Hs2.
destruct (cno_tfacts cx ly3 S3 W3 (ms_mem ms3) md3 a b t Hb HAR Hab)
  as (Hreq & HtIn & HtNot & Ht4096 & Htc & Htapp & Htp & HaIn & HbIn & Ha4096 & Hac & Hb4096 & Hbc & Hat & Hbt & Hd0).
set (x2 := t + cno_n cx + 17).
assert (Hx2m : t <= x2 < t + (cno_n cx + 18)) by (unfold x2; lia).
assert (Hx2b : 4096 <= x2 /\ x2 + 1 <= alloc_ceiling) by (unfold x2; lia).
destruct (Hrad x2 ltac:(unfold x2; lia)) as (sv & Hsvv & Hsaddr).
assert (Hsvr : 0 <= sv <= 7).
{ unfold saddr_ok in Hsaddr. pose proof (Z.mod_pos_bound x2 8 ltac:(lia)).
  destruct Hsaddr as [-> | (Q1 & Q2)]; lia. }
(* the geometry of the stored byte and of its shadow byte *)
assert (Hq8 : 8 * (x2 / 8) <= x2 < 8 * (x2 / 8) + 8) by (Z.div_mod_to_equations; lia).
assert (HqF : 8 * (cno_F cx / 8) = cno_F cx) by (Z.div_mod_to_equations; lia).
assert (HSFv : cno_SF cx = SHADOW_OFF + cno_F cx / 8) by (unfold cno_SF, shadow_addr; reflexivity).
assert (HxF : x2 + 1 <= cno_F cx \/ cno_F cx + 128 <= x2).
{ pose proof (sep_block_frame tfibsegs B LAWS ly3 S3 W3 (unpoison (c_U cx) (ms_mem ms3)) md3 t (cno_n cx + 18) 1
    (c_fpos cx) HAR HtIn Hin) as Hd.
  rewrite EFa in Hd. change (fs_frame_bytes 1) with 128 in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  rewrite Hreq in Hd. unfold x2. lia. }
assert (Hlowhigh : x2 + 1 <= kLowShadowBeg \/ kHighMemBeg <= x2).
{ destruct Htapp as (_ & [Hlo | (Hh1 & Hh2)]); [left | right]; unfold x2 in *; lia. }
unfold kLowShadowBeg, kHighMemBeg in Hlowhigh.
assert (Hx2sh : x2 + 1 <= SHADOW_OFF + x2 / 8 \/ SHADOW_OFF + x2 / 8 + 1 <= x2).
{ unfold SHADOW_OFF in *. destruct Hlowhigh as [H | H]; [left | right]; lia. }
assert (HshF : SHADOW_OFF + x2 / 8 + 1 <= cno_F cx \/ cno_F cx + 128 <= SHADOW_OFF + x2 / 8).
{ destruct HFapp as (_ & [Hlo | (Hh1 & Hh2)]);
  unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *; [right | left]; lia. }
assert (HshSF : SHADOW_OFF + x2 / 8 + 1 <= cno_SF cx \/ cno_SF cx + 16 <= SHADOW_OFF + x2 / 8).
{ rewrite HSFv. destruct HxF as [H | H]; [left | right]; lia. }
(* the env with the inline check's four atoms *)
set (E' := havoc E 51 [w64 x2; w64 (x2 / 8); w64 (SHADOW_OFF + x2 / 8); w64 sv]).
assert (Hold : forall q, (q < 51)%nat -> ew E' q = ew E q) by (intros q Hq; apply ew_havoc_old; lia).
assert (F51 : ew E' 51 = w64 x2) by (unfold E', havoc; cbn [ew]; reflexivity).
assert (F52 : ew E' 52 = w64 (x2 / 8)) by (unfold E', havoc; cbn [ew]; reflexivity).
assert (F53 : ew E' 53 = w64 (SHADOW_OFF + x2 / 8)) by (unfold E', havoc; cbn [ew]; reflexivity).
assert (F54 : ew E' 54 = w64 sv) by (unfold E', havoc; cbn [ew]; reflexivity).
assert (U8' : bv_unsigned (ew E' 8) = cno_sp0 cx)
  by (rewrite (Hold 8%nat ltac:(lia)), C8; unfold w64; apply wz; lia).
assert (U9' : bv_unsigned (ew E' 9) = cno_sp1 cx)
  by (rewrite (Hold 9%nat ltac:(lia)), C9; unfold w64; apply wz; lia).
assert (U19' : bv_unsigned (ew E' 19) = cno_F cx)
  by (rewrite (Hold 19%nat ltac:(lia)), C19; unfold w64; apply wz; lia).
assert (U18' : bv_unsigned (ew E' 18) = cno_SF cx)
  by (rewrite (Hold 18%nat ltac:(lia)), C18; unfold w64; apply wz; unfold cno_SF in *; lia).
assert (U51' : bv_unsigned (ew E' 51) = x2) by (rewrite F51; unfold w64; apply wz; lia).
assert (U53' : bv_unsigned (ew E' 53) = SHADOW_OFF + x2 / 8)
  by (rewrite F53; unfold w64; apply wz; unfold SHADOW_OFF; lia).
assert (HE' : cno_E cx E').
{ pose proof HE as (X32 & X33 & X46 & X47). split; [rewrite (Hold 32%nat ltac:(lia)); exact X32|].
  split; [intros j Hj; rewrite (Hold (33 + j)%nat ltac:(lia)); exact (X33 j Hj)|].
  split; [rewrite (Hold 46%nat ltac:(lia)); exact X46 | rewrite (Hold 47%nat ltac:(lia)); exact X47]. }
(* the state with the inline check's regions and facts *)
assert (HS0 : st_ok tfibsegs E' ss_S (restrict (w_H W3) ms3))
  by (unfold E'; apply st_ok_havoc_win; [exact HS | vm_compute; reflexivity]).
assert (HSA : st_ok tfibsegs E'
  (mkSS (ss_pc ss_S) (ss_regs ss_S) (ss_mem ss_S ++ [cno_RX; cno_RSH]) (ss_resv ss_S) (ss_facts ss_S))
  (restrict (w_H W3) ms3)).
{ apply (cno_app_regions E' ss_S _ [cno_RX; cno_RSH] HS0).
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold cno_RX, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U51'. cbn [ms_mem restrict]. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. replace (x2 + o) with x2 by lia.
      destruct (Htp x2 Hx2m) as (Hpres & Hnown).
      apply (apresent_writable tfibsegs).
      exact (fsw_apresent_notowned B ly3 S3 (c_U cx) W3 (ms_mem ms3) md3 x2 HARU ltac:(lia) Hnown Hpres).
    + unfold cno_RSH, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U53'.
      cbn [ms_mem restrict]. split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|].
      split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val tfibsegs E' _ _ 0 1 (SOff 54 0) sv);
        [rewrite fsw_SOff0, F54; reflexivity | cbn; lia | cbn; lia|].
      rewrite Z.add_0_r. apply cno_vm1. exact Hsvv.
  - cbn [pairwise_disjoint all_disjoint]. split; [split; [|exact I] | split; [exact I | exact I]].
    unfold extent_disjoint, cno_RX, cno_RSH. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U51', U53'. unfold SHADOW_OFF in *. lia.
  - intros r1 r2 Hr1 Hr2.
    unfold ss_S, cno_ss, fss_ret_s0_args, fss_ret_s0_regs, fs_ret_s0_region, cno_fr_region, cno_sh_region,
      cno_sl_region in Hr1.
    cbn [ss_mem] in Hr1.
    destruct Hr2 as [<- | [<- | []]]; destruct Hr1 as [<- | [<- | [<- | [<- | []]]]];
      unfold extent_disjoint, cno_RX, cno_RSH;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
      rewrite ?U8', ?U19', ?U18', ?U9', ?U51', ?U53';
      try unfold cno_SF in *; try unfold shadow_addr in *; try unfold SHADOW_OFF in *; lia. }
assert (U21' : bv_unsigned (ew E' 21) = t)
  by (rewrite (Hold 21%nat ltac:(lia)), E21; unfold w64; apply wz; lia).
assert (U22' : bv_unsigned (ew E' 22) = cno_n cx + 17)
  by (rewrite (Hold 22%nat ltac:(lia)), E22; unfold w64; apply wz; lia).
assert (U23' : bv_unsigned (ew E' 23) = 2 ^ 64 - 1 - t)
  by (rewrite (Hold 23%nat ltac:(lia)), E23; unfold w64; apply wz; lia).
assert (U52' : bv_unsigned (ew E' 52) = x2 / 8) by (rewrite F52; unfold w64; apply wz; lia).
assert (U54' : bv_unsigned (ew E' 54) = sv) by (rewrite F54; unfold w64; apply wz; lia).
assert (A51 : afact_ok E' 51 (mkAF 4096 (2 ^ 48) 0)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U51'.
  split; [lia|]. split; [rewrite Z.pow_0_r; apply Z.mod_1_r | lia]. }
assert (A52 : afact_ok E' 52 (mkAF 0 (2 ^ 45) 0)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U52'.
  split; [lia|]. split; [rewrite Z.pow_0_r; apply Z.mod_1_r | lia]. }
assert (A53 : afact_ok E' 53 (mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 0)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U53'.
  split; [unfold SHADOW_OFF; lia|]. split; [rewrite Z.pow_0_r; apply Z.mod_1_r | lia]. }
assert (A54 : afact_ok E' 54 (mkAF 0 7 0)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U54'.
  split; [lia|]. split; [rewrite Z.pow_0_r; apply Z.mod_1_r | lia]. }
assert (A21 : afact_ok E' 21 (mkAF 4096 (2 ^ 47) 0)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U21'.
  split; [lia|]. split; [rewrite Z.pow_0_r; apply Z.mod_1_r | lia]. }
assert (A22 : afact_ok E' 22 (mkAF 0 (PRESET_FILE_MAX_BYTES + 17) 0)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U22'.
  split; [unfold PRESET_FILE_MAX_BYTES; lia|]. split; [rewrite Z.pow_0_r; apply Z.mod_1_r | lia]. }
assert (A23 : afact_ok E' 23 (mkAF (2 ^ 64 - 1 - 2 ^ 47) (2 ^ 64 - 1) 0)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U23'.
  split; [lia|]. split; [rewrite Z.pow_0_r; apply Z.mod_1_r | lia]. }
assert (A8 : afact_ok E' 8 (mkAF (2 ^ 46) (2 ^ 47) 4)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U8'.
  split; [lia|]. split; [change (2 ^ 4) with 16; exact N1 | lia]. }
assert (A19 : afact_ok E' 19 (mkAF 4096 (2 ^ 47) 5)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U19'.
  split; [lia|]. split; [change (2 ^ 5) with 32; exact Hal32 | lia]. }
assert (A18 : afact_ok E' 18 (mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 0)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U18'.
  split; [unfold cno_SF, SHADOW_OFF in *; lia|]. split; [rewrite Z.pow_0_r; apply Z.mod_1_r | lia]. }
assert (HSB : st_ok tfibsegs E' ss_S1 (restrict (w_H W3) ms3)).
{ unfold ss_S1. apply st_ok_set_facts; [exact HSA|]. unfold cno_GS.
  split; [|split; [cbn; exact I|]].
  - cbn [f_atoms atoms_ok ss_S cno_ss fss_ret_s0_args ss_facts cno_gf].
    exact (conj A51 (conj A52 (conj A53 (conj A54 (conj A21 (conj A22 (conj A23
      (conj A8 (conj A19 (conj A18 I)))))))))).
  - cbn [f_alias alias_ok]. split; [|split; [|split; [|exact I]]].
    + apply U_inj. rewrite U_SAlu, (U_atom E' 21 t ltac:(rewrite (Hold 21%nat ltac:(lia)); exact E21) ltac:(lia)),
        (U_atom E' 22 (cno_n cx + 17) ltac:(rewrite (Hold 22%nat ltac:(lia)); exact E22) ltac:(lia)),
        (U_atom E' 51 x2 F51 ltac:(lia)).
      cbn [zalu_raw]. rewrite (zcanon_id (t + (cno_n cx + 17)) ltac:(unfold M64; lia)). unfold x2. lia.
    + apply U_inj. rewrite U_srl3, (U_atom E' 51 x2 F51 ltac:(lia)), (U_atom E' 52 (x2 / 8) F52 ltac:(lia)).
      reflexivity.
    + apply U_inj. rewrite U_SAlu, (U_atom E' 52 (x2 / 8) F52 ltac:(lia)),
        (U_atom E' 24 SHADOW_OFF ltac:(rewrite (Hold 24%nat ltac:(lia)); exact E24) ltac:(unfold SHADOW_OFF; lia)),
        (U_atom E' 53 (SHADOW_OFF + x2 / 8) F53 ltac:(unfold SHADOW_OFF; lia)).
      cbn [zalu_raw]. rewrite (Z.add_comm (x2 / 8) SHADOW_OFF).
      apply zcanon_id. unfold M64, SHADOW_OFF in *. lia. }
pose proof HARU as HARU0.
assert (Hcore' : cno_core cx E').
{ unfold cno_core. rewrite (Hold 2%nat ltac:(lia)), (Hold 8%nat ltac:(lia)), (Hold 9%nat ltac:(lia)),
    (Hold 18%nat ltac:(lia)), (Hold 19%nat ltac:(lia)), (Hold 3%nat ltac:(lia)), (Hold 4%nat ltac:(lia)).
  repeat split; assumption. }
assert (E20' : ew E' 20 = w64 b) by (rewrite (Hold 20%nat ltac:(lia)); exact E20).
assert (E21' : ew E' 21 = w64 t) by (rewrite (Hold 21%nat ltac:(lia)); exact E21).
assert (E25' : ew E' 25 = w64 (cno_F cx)) by (rewrite (Hold 25%nat ltac:(lia)); exact E25).
assert (E48' : ew E' 48 = w64 a) by (rewrite (Hold 48%nat ltac:(lia)); exact E48).
(* ---- the common tail of the two arms: the machine at the first decode, INV_D1, and the next span ---- *)
assert (TAIL : forall (ssF : sstate) (ms' : machine_state) (mat' : list word),
  st_ok tfibsegs E' ssF (restrict (w_H W3) ms') ->
  ss_pc ssF = A_preset_base64_decode ->
  (forall r : bv 5, In r cno_D_regs -> sr_get (ss_regs ssF) r = sr_get (ss_regs ss_D) r) ->
  ss_mem ssF = ss_mem ss_D ->
  ss_resv ssF = None ->
  cno_J B cx 3 ly3 S3 W3 (unpoison (c_U cx) (ms_mem ms')) (with_vm_backing (m_vm_lazy md3) mat' md3) ->
  ARU tfibsegs B ly3 S3 (c_U cx) W3 (ms_mem ms') (with_vm_backing (m_vm_lazy md3) mat' md3) ->
  frame_of E' (ss_mem ss_S ++ [cno_RX; cno_RSH]) (ms_mem ms3) (ms_mem ms') ->
  SRr tfibsegs W3 (mkCfg ms' (with_vm_backing (m_vm_lazy md3) mat' md3)) (cno_post B cx)).
{ intros ssF ms' mat' HSF Hpc Hrg Hmm Hrv HJ' HARU' HFF.
  destruct (cno_keepX cx E' 0x813f8 cno_flag_chunk cno_sl18 ly3 S3 (c_U cx) W3 (ms_mem ms3) md3 x2
    (ms_mem ms3) (ms_mem ms') Hb HARU0 Hin EF U8' U9' U19' U18' U51' HFF) as (KL & KB).
  (* a byte of the walk's own block is no byte of the allocator's statics *)
  assert (Hxfp : ~ inFP FS_PSTAT_FP x2)
    by (apply (cno_blk_offfp ly3 S3 W3 (unpoison (c_U cx) (ms_mem ms3)) md3 t (cno_n cx + 18) x2 HAR HtIn);
        rewrite Hreq; unfold x2; lia).
  assert (Hg' : fs_glob tfibsegs W3 (ms_mem ms') (c_live cx) (c_peak cx) (c_cnt cx) (c_fail cx)).
  { apply (cno_glob_ledger W3 W3 (ms_mem ms3) (ms_mem ms') _ _ _ _); [|exact Hg].
    intros y Hy. apply (aview_at tfibsegs (w_H W3) (ms_mem ms') (ms_mem ms3) y).
    apply KL; [exact Hy | intros Ey; apply Hxfp; rewrite <- Ey; exact Hy]. }
  assert (Hza' : zbytes_at tfibsegs W3 (ms_mem ms') a (pn_copy (c_db cx) 65)).
  { apply (cno_zb_kept W3 (ms_mem ms3) (ms_mem ms') a _ Hza).
    intros j Hj. rewrite (cno_pn_length (c_db cx) 65) in Hj.
    exact (KB a (cno_n cx + 18) j HaIn ltac:(rewrite Hreq; unfold cno_n in *; lia) ltac:(unfold x2, cno_n in *; lia)). }
  assert (Hzb' : zbytes_at tfibsegs W3 (ms_mem ms') b (pn_copy (c_db cx) 66)).
  { apply (cno_zb_kept W3 (ms_mem ms3) (ms_mem ms') b _ Hzb).
    intros j Hj. rewrite (cno_pn_length (c_db cx) 66) in Hj.
    exact (KB b (cno_n cx + 18) j HbIn ltac:(rewrite Hreq; unfold cno_n in *; lia) ltac:(unfold x2, cno_n in *; lia)). }
  assert (Hzt' : zbytes_at tfibsegs W3 (ms_mem ms') t (c_db cx ++ repeat 0 18%nat)).
  { assert (Esplit : c_db cx ++ repeat 0 18%nat = (c_db cx ++ repeat 0 17%nat) ++ [0]).
    { rewrite <- app_assoc. f_equal.
      all: try (replace 18%nat with (17 + 1)%nat by lia; rewrite repeat_app; reflexivity). }
    rewrite Esplit.
    apply (cno_zb_ext0 W3 (ms_mem ms3) (ms_mem ms') t (c_db cx ++ repeat 0 17%nat) (cno_n cx + 17) Hzt).
    - rewrite length_app, repeat_length. unfold cno_n. lia.
    - intros j Hj.
      exact (KB t (cno_n cx + 18) j HtIn ltac:(rewrite Hreq; lia) ltac:(unfold x2 in *; lia)).
    - set (rX := nth 4 (ss_mem ss_D) (YP09.mkRegion None 0 0 0 0 [])).
      assert (HrX : nth_error (ss_mem ssF) 4 = Some rX) by (rewrite Hmm; vm_compute; reflexivity).
      assert (HcX : YP09.chunk_ok tfibsegs E' (mrestrict (w_H W3) (ms_mem ms')) (bv_unsigned (ew E' 51))
        (YP09.mkChunk 0 (CVal 1 (SLit 0))))
        by (apply (cno_chunk_at E' ssF (w_H W3) ms' 4 rX 51 (YP09.mkChunk 0 (CVal 1 (SLit 0))) HSF HrX
             ltac:(vm_compute; reflexivity) ltac:(vm_compute; tauto))).
      rewrite U51' in HcX.
      pose proof (val_of_chunk_ok tfibsegs E' (mrestrict (w_H W3) (ms_mem ms')) x2 0 1 (SLit 0) 0 HcX
        ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as HV.
      rewrite Z.add_0_r in HV. replace (t + (cno_n cx + 17)) with x2 by (unfold x2; lia). exact HV. }
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W3) E' ssF ms' HSF Hrv), Hpc.
  change (mkCfg (mkst (ms_regs ms') (Z_to_bv 64 A_preset_base64_decode) (ms_mem ms') (seg_rom tfibsegs))
            (with_vm_backing (m_vm_lazy md3) mat' md3))
    with (cfg_at tfibsegs A_preset_base64_decode (ms_regs ms') (ms_mem ms')
            (with_vm_backing (m_vm_lazy md3) mat' md3)).
  apply (HD1 cx 3 ly3 S3 (c_U cx) W3 (ms_regs ms') (ms_mem ms')
          (with_vm_backing (m_vm_lazy md3) mat' md3) Hb).
  exact (cno_segM_D1 cx E' ly3 S3 W3 ms' (with_vm_backing (m_vm_lazy md3) mat' md3) a b t ssF
    Hb HE' HJ' HARU' Hh Hab Hcore' E20' E21' E25' E48' Hza' Hzb' Hzt' Hg' Hpc Hrg Hmm HSF). }
(* ---- the two arms of the inline check 0x81404-0x81410 ---- *)
destruct (Z.eq_dec sv 0) as [Hsv0 | Hsv0].
- (* 00: the check falls through to 0x81414 *)
  assert (HSC : st_ok tfibsegs E' (add_cond ss_S1 (mkAC BC_EQ (SOff 54 0) (SLit 0))) (restrict (w_H W3) ms3)).
  { change (mkAC BC_EQ (SOff 54 0) (SLit 0)) with (mkAC (neg_bc BC_NE) (SOff 54 0) (SLit 0)).
    apply (st_ok_add_cond_neg tfibsegs E' ss_S1 _ BC_NE (SOff 54 0) (SLit 0) HSB).
    rewrite branch_ne_U, (U_atom E' 54 sv F54 ltac:(lia)), U_SLit, Hsv0. vm_compute. reflexivity. }
  fsw_aj_run_toU cno_tbl_ok HSC HJ HARU A_preset_base64_decode.
  { change (ss_mem (add_cond ss_S1 (mkAC BC_EQ (SOff 54 0) (SLit 0))))
      with (ss_mem ss_S ++ [cno_RX; cno_RSH]).
    apply awr_ok_app.
    - eapply (cno_awr_ss B E' _ _ _ _ _ ly3 _ (c_fpos cx) (cno_F cx) (cno_sp1 cx) 0x813f8 cno_flag_chunk
        cno_sl18 U8' U19' U18' U9' (eq_sym EFa)); lia.
    - eapply (awr_ok_cons_gen tfibsegs B E' cno_RX [cno_RSH] _ _ _ _ _ _ _ _ 51%nat x2);
        [reflexivity | exact U51' | | apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]].
      intros y Hy. cbn [YP09.r_wlo YP09.r_whi cno_RX] in Hy.
      left. right. right. left. exists t, (cno_n cx + 18).
      split; [exact HtIn|]. split; [exact HtNot|]. rewrite Hreq. unfold x2 in *. lia. }
  eapply (TAIL _ ms mat);
    [exact HSC | vm_compute; reflexivity
     | intros r Hr; cbv [cno_D_regs In] in Hr; repeat (destruct Hr as [<- | Hr]); try destruct Hr;
       vm_compute; reflexivity
     | vm_compute; reflexivity | vm_compute; reflexivity | exact HJ | exact HARU | exact HF].
- (* not 00: the slow path 0x8160c-0x81610, whose `blt a2,a1` is taken back to 0x81414 (saddr_ok) *)
  assert (HSC : st_ok tfibsegs E'
    (add_cond (add_cond ss_S1 (mkAC BC_NE (SOff 54 0) (SLit 0)))
       (mkAC BC_LT (SAlu ALU_AND (SOff 51 0) (SLit 7)) (SOff 54 0))) (restrict (w_H W3) ms3)).
  { apply (st_ok_add_cond tfibsegs E' _ _ BC_LT (SAlu ALU_AND (SOff 51 0) (SLit 7)) (SOff 54 0)).
    - apply (st_ok_add_cond tfibsegs E' ss_S1 _ BC_NE (SOff 54 0) (SLit 0) HSB).
      rewrite branch_ne_U, (U_atom E' 54 sv F54 ltac:(lia)), U_SLit.
      change (zcanon 0) with 0. destruct (Z.eqb_spec sv 0) as [Hz | Hz]; [destruct (Hsv0 Hz) | reflexivity].
    - assert (Hlt : x2 mod 8 < sv).
      { unfold saddr_ok in Hsaddr. destruct Hsaddr as [Hz | (Q1 & Q2)]; [destruct (Hsv0 Hz) | exact Q1]. }
      pose proof (Z.mod_pos_bound x2 8 ltac:(lia)) as Hmb.
      assert (UA : U E' (SAlu ALU_AND (SOff 51 0) (SLit 7)) = x2 mod 8).
      { rewrite U_and_lit by lia. rewrite (U_atom E' 51 x2 F51 ltac:(lia)). apply cno_land7. lia. }
      assert (UB : U E' (SOff 54 0) = sv) by exact (U_atom E' 54 sv F54 ltac:(lia)).
      unfold U in UA, UB.
      cbn [branch_taken]. rewrite bv_lts_signed.
      rewrite (signed_of_small _ ltac:(rewrite UA; unfold half64; lia)),
              (signed_of_small _ ltac:(rewrite UB; unfold half64; lia)).
      rewrite UA, UB. apply Z.ltb_lt. lia. }
  fsw_aj_run_toU cno_tbl_ok HSC HJ HARU A_preset_base64_decode.
  { change (ss_mem (add_cond (add_cond ss_S1 (mkAC BC_NE (SOff 54 0) (SLit 0)))
              (mkAC BC_LT (SAlu ALU_AND (SOff 51 0) (SLit 7)) (SOff 54 0))))
      with (ss_mem ss_S ++ [cno_RX; cno_RSH]).
    apply awr_ok_app.
    - eapply (cno_awr_ss B E' _ _ _ _ _ ly3 _ (c_fpos cx) (cno_F cx) (cno_sp1 cx) 0x813f8 cno_flag_chunk
        cno_sl18 U8' U19' U18' U9' (eq_sym EFa)); lia.
    - eapply (awr_ok_cons_gen tfibsegs B E' cno_RX [cno_RSH] _ _ _ _ _ _ _ _ 51%nat x2);
        [reflexivity | exact U51' | | apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]].
      intros y Hy. cbn [YP09.r_wlo YP09.r_whi cno_RX] in Hy.
      left. right. right. left. exists t, (cno_n cx + 18).
      split; [exact HtIn|]. split; [exact HtNot|]. rewrite Hreq. unfold x2 in *. lia. }
  eapply (TAIL _ ms mat);
    [exact HSC | vm_compute; reflexivity
     | intros r Hr; cbv [cno_D_regs In] in Hr; repeat (destruct Hr as [<- | Hr]); try destruct Hr;
       vm_compute; reflexivity
     | vm_compute; reflexivity | vm_compute; reflexivity | exact HJ | exact HARU | exact HF].
Qed.

(* ---- 0x813bc -> 0x813f8: `not s7,s5`, U1, the first inline check (both arms), the store t[n] = 0, U2 and the
   __asan_memset call ---- *)
Lemma cno_seg_M2 : cno_from B ss_S INV_S -> cno_from B ss_C INV_C.
Proof.
intros HNX cx E k ly3 S3 U3 W3 ms3 md3 Hb HE HJ HARU HINV HS.
destruct HINV as (a & b & t & -> & -> & Hab & Hh & Hcore & E10 & E20 & E22 & E24 & E25 & E48 & E49 & E50
  & Hza & Hzb & Hzt & Hrad & Hg).
pose proof (cno_nums B cx Hb) as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
pose proof asan_consts as (CA1 & CA2 & CA3 & CA4 & CA5). pose proof cno_stk as FS.
pose proof Hb as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HnM & _).
unfold PRESET_FILE_MAX_BYTES in HnM.
assert (Hn0 : 0 <= cno_n cx) by (unfold cno_n; lia).
pose proof Hcore as (C2 & C8 & C9 & C18 & C19 & C3 & C4).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _).
assert (Hin : In (1, c_fpos cx) (frames S3)) by (rewrite Hfrs; left; reflexivity).
assert (EF : ly_F ly3 = ly_F (c_ly cx)) by (destruct Hly as (_ & _ & _ & _ & _ & X & _); exact X).
assert (EFa : frame_addr ly3 1 (c_fpos cx) = cno_F cx) by (unfold cno_F, frame_addr; rewrite EF; reflexivity).
destruct (frames_bounds tfibsegs B LAWS ly3 S3 W3 (unpoison (c_U cx) (ms_mem ms3)) md3 1 (c_fpos cx) HAR Hin)
  as (HF4096 & HFceil & HFapp).
rewrite EFa in HF4096, HFceil, HFapp. change (fs_frame_bytes 1) with 128 in HF4096, HFceil, HFapp.
destruct (al_frames _ _ LAWS ly3 S3 W3 (unpoison (c_U cx) (ms_mem ms3)) md3 1 (c_fpos cx) HAR Hin)
  as (Hal32 & _ & _ & _).
rewrite EFa in Hal32.
assert (HF64 : 0 <= cno_F cx < 2 ^ 64) by (unfold in_app, kLowShadowBeg, ASAN_CEIL in HFapp; lia).
pose proof (shadow_addr_bounds (cno_F cx) ltac:(unfold kHighMemEnd; lia)) as (Hs1 & Hs2).
unfold kLowMemEnd, kHighShadowEnd in Hs1, Hs2.
destruct (cno_tfacts cx ly3 S3 W3 (ms_mem ms3) md3 a b t Hb HAR Hab)
  as (Hreq & HtIn & HtNot & Ht4096 & Htc & Htapp & Htp & HaIn & HbIn & Ha4096 & Hac & Hb4096 & Hbc & Hat & Hbt & Hd0).
set (x1 := t + cno_n cx).
assert (Hx1m : t <= x1 < t + (cno_n cx + 18)) by (unfold x1; lia).
assert (Hx1b : 4096 <= x1 /\ x1 + 1 <= alloc_ceiling) by (unfold x1; lia).
destruct (Hrad x1 ltac:(unfold x1; lia)) as (sv & Hsvv & Hsaddr).
assert (Hsvr : 0 <= sv <= 7).
{ unfold saddr_ok in Hsaddr. pose proof (Z.mod_pos_bound x1 8 ltac:(lia)).
  destruct Hsaddr as [-> | (Q1 & Q2)]; lia. }
assert (Hq8 : 8 * (x1 / 8) <= x1 < 8 * (x1 / 8) + 8) by (Z.div_mod_to_equations; lia).
assert (HqF : 8 * (cno_F cx / 8) = cno_F cx) by (Z.div_mod_to_equations; lia).
assert (HSFv : cno_SF cx = SHADOW_OFF + cno_F cx / 8) by (unfold cno_SF, shadow_addr; reflexivity).
assert (HxF : x1 + 1 <= cno_F cx \/ cno_F cx + 128 <= x1).
{ pose proof (sep_block_frame tfibsegs B LAWS ly3 S3 W3 (unpoison (c_U cx) (ms_mem ms3)) md3 t (cno_n cx + 18) 1
    (c_fpos cx) HAR HtIn Hin) as Hd.
  rewrite EFa in Hd. change (fs_frame_bytes 1) with 128 in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  rewrite Hreq in Hd. unfold x1. lia. }
assert (Hlowhigh : x1 + 1 <= kLowShadowBeg \/ kHighMemBeg <= x1).
{ destruct Htapp as (_ & [Hlo | (Hh1 & Hh2)]); [left | right]; unfold x1 in *; lia. }
unfold kLowShadowBeg, kHighMemBeg in Hlowhigh.
assert (Hx1sh : x1 + 1 <= SHADOW_OFF + x1 / 8 \/ SHADOW_OFF + x1 / 8 + 1 <= x1).
{ unfold SHADOW_OFF in *. destruct Hlowhigh as [H | H]; [left | right]; lia. }
assert (HshF : SHADOW_OFF + x1 / 8 + 1 <= cno_F cx \/ cno_F cx + 128 <= SHADOW_OFF + x1 / 8).
{ destruct HFapp as (_ & [Hlo | (Hh1 & Hh2)]);
  unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *; [right | left]; lia. }
assert (HshSF : SHADOW_OFF + x1 / 8 + 1 <= cno_SF cx \/ cno_SF cx + 16 <= SHADOW_OFF + x1 / 8).
{ rewrite HSFv. destruct HxF as [H | H]; [left | right]; lia. }
(* the env with the inline check's five atoms (51 .. 55, the last being ~t) *)
set (E' := havoc E 51 [w64 x1; w64 (x1 / 8); w64 (SHADOW_OFF + x1 / 8); w64 sv; w64 (2 ^ 64 - 1 - t)]).
assert (Hold : forall q, (q < 51)%nat -> ew E' q = ew E q) by (intros q Hq; apply ew_havoc_old; lia).
assert (F51 : ew E' 51 = w64 x1) by (unfold E', havoc; cbn [ew]; reflexivity).
assert (F52 : ew E' 52 = w64 (x1 / 8)) by (unfold E', havoc; cbn [ew]; reflexivity).
assert (F53 : ew E' 53 = w64 (SHADOW_OFF + x1 / 8)) by (unfold E', havoc; cbn [ew]; reflexivity).
assert (F54 : ew E' 54 = w64 sv) by (unfold E', havoc; cbn [ew]; reflexivity).
assert (F55 : ew E' 55 = w64 (2 ^ 64 - 1 - t)) by (unfold E', havoc; cbn [ew]; reflexivity).
assert (U8' : bv_unsigned (ew E' 8) = cno_sp0 cx)
  by (rewrite (Hold 8%nat ltac:(lia)), C8; unfold w64; apply wz; lia).
assert (U9' : bv_unsigned (ew E' 9) = cno_sp1 cx)
  by (rewrite (Hold 9%nat ltac:(lia)), C9; unfold w64; apply wz; lia).
assert (U19' : bv_unsigned (ew E' 19) = cno_F cx)
  by (rewrite (Hold 19%nat ltac:(lia)), C19; unfold w64; apply wz; lia).
assert (U18' : bv_unsigned (ew E' 18) = cno_SF cx)
  by (rewrite (Hold 18%nat ltac:(lia)), C18; unfold w64; apply wz; unfold cno_SF in *; lia).
assert (U51' : bv_unsigned (ew E' 51) = x1) by (rewrite F51; unfold w64; apply wz; lia).
assert (U53' : bv_unsigned (ew E' 53) = SHADOW_OFF + x1 / 8)
  by (rewrite F53; unfold w64; apply wz; unfold SHADOW_OFF; lia).
assert (U52' : bv_unsigned (ew E' 52) = x1 / 8) by (rewrite F52; unfold w64; apply wz; lia).
assert (U54' : bv_unsigned (ew E' 54) = sv) by (rewrite F54; unfold w64; apply wz; lia).
assert (U55' : bv_unsigned (ew E' 55) = 2 ^ 64 - 1 - t) by (rewrite F55; unfold w64; apply wz; lia).
assert (U10' : bv_unsigned (ew E' 10) = t)
  by (rewrite (Hold 10%nat ltac:(lia)), E10; unfold w64; apply wz; lia).
assert (U22' : bv_unsigned (ew E' 22) = cno_n cx)
  by (rewrite (Hold 22%nat ltac:(lia)), E22; unfold w64; apply wz; lia).
assert (HE' : cno_E cx E').
{ pose proof HE as (X32 & X33 & X46 & X47). split; [rewrite (Hold 32%nat ltac:(lia)); exact X32|].
  split; [intros j Hj; rewrite (Hold (33 + j)%nat ltac:(lia)); exact (X33 j Hj)|].
  split; [rewrite (Hold 46%nat ltac:(lia)); exact X46 | rewrite (Hold 47%nat ltac:(lia)); exact X47]. }
assert (Hcore' : cno_core cx E').
{ unfold cno_core. rewrite (Hold 2%nat ltac:(lia)), (Hold 8%nat ltac:(lia)), (Hold 9%nat ltac:(lia)),
    (Hold 18%nat ltac:(lia)), (Hold 19%nat ltac:(lia)), (Hold 3%nat ltac:(lia)), (Hold 4%nat ltac:(lia)).
  repeat split; assumption. }
assert (E20' : ew E' 20 = w64 b) by (rewrite (Hold 20%nat ltac:(lia)); exact E20).
assert (E24' : ew E' 24 = w64 SHADOW_OFF) by (rewrite (Hold 24%nat ltac:(lia)); exact E24).
assert (E25' : ew E' 25 = w64 (cno_F cx)) by (rewrite (Hold 25%nat ltac:(lia)); exact E25).
assert (E48' : ew E' 48 = w64 a) by (rewrite (Hold 48%nat ltac:(lia)); exact E48).
(* the state with the inline check's regions and facts *)
assert (HS0 : st_ok tfibsegs E' ss_C (restrict (w_H W3) ms3))
  by (unfold E'; apply st_ok_havoc_win; [exact HS | vm_compute; reflexivity]).
assert (HSA : st_ok tfibsegs E'
  (mkSS (ss_pc ss_C) (ss_regs ss_C) (ss_mem ss_C ++ [cno_RX; cno_RSH]) (ss_resv ss_C) (ss_facts ss_C))
  (restrict (w_H W3) ms3)).
{ apply (cno_app_regions E' ss_C _ [cno_RX; cno_RSH] HS0).
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold cno_RX, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U51'. cbn [ms_mem restrict]. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. replace (x1 + o) with x1 by lia.
      destruct (Htp x1 Hx1m) as (Hpres & Hnown).
      apply (apresent_writable tfibsegs).
      exact (fsw_apresent_notowned B ly3 S3 (c_U cx) W3 (ms_mem ms3) md3 x1 HARU ltac:(lia) Hnown Hpres).
    + unfold cno_RSH, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U53'.
      cbn [ms_mem restrict]. split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|].
      split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val tfibsegs E' _ _ 0 1 (SOff 54 0) sv);
        [rewrite fsw_SOff0, F54; reflexivity | cbn; lia | cbn; lia|].
      rewrite Z.add_0_r. apply cno_vm1. exact Hsvv.
  - cbn [pairwise_disjoint all_disjoint]. split; [split; [|exact I] | split; [exact I | exact I]].
    unfold extent_disjoint, cno_RX, cno_RSH. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U51', U53'. unfold SHADOW_OFF in *. lia.
  - intros r1 r2 Hr1 Hr2.
    unfold ss_C, cno_ss, fss_ret_s0_args, fss_ret_s0_regs, fs_ret_s0_region, cno_fr_region, cno_sh_region,
      cno_sl_region in Hr1.
    cbn [ss_mem] in Hr1.
    destruct Hr2 as [<- | [<- | []]]; destruct Hr1 as [<- | [<- | [<- | [<- | []]]]];
      unfold extent_disjoint, cno_RX, cno_RSH;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
      rewrite ?U8', ?U19', ?U18', ?U9', ?U51', ?U53';
      try unfold cno_SF in *; try unfold shadow_addr in *; try unfold SHADOW_OFF in *; lia. }
assert (A51 : afact_ok E' 51 (mkAF 4096 (2 ^ 48) 0)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U51'.
  split; [lia|]. split; [rewrite Z.pow_0_r; apply Z.mod_1_r | lia]. }
assert (A52 : afact_ok E' 52 (mkAF 0 (2 ^ 45) 0)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U52'.
  split; [lia|]. split; [rewrite Z.pow_0_r; apply Z.mod_1_r | lia]. }
assert (A53 : afact_ok E' 53 (mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 0)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U53'.
  split; [unfold SHADOW_OFF; lia|]. split; [rewrite Z.pow_0_r; apply Z.mod_1_r | lia]. }
assert (A54 : afact_ok E' 54 (mkAF 0 7 0)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U54'.
  split; [lia|]. split; [rewrite Z.pow_0_r; apply Z.mod_1_r | lia]. }
assert (A55 : afact_ok E' 55 (mkAF (2 ^ 64 - 1 - 2 ^ 47) (2 ^ 64 - 1) 0)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U55'.
  split; [lia|]. split; [rewrite Z.pow_0_r; apply Z.mod_1_r | lia]. }
assert (A10 : afact_ok E' 10 (mkAF 4096 (2 ^ 47) 0)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U10'.
  split; [lia|]. split; [rewrite Z.pow_0_r; apply Z.mod_1_r | lia]. }
assert (A22 : afact_ok E' 22 (mkAF 0 PRESET_FILE_MAX_BYTES 0)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U22'.
  split; [unfold PRESET_FILE_MAX_BYTES; lia|]. split; [rewrite Z.pow_0_r; apply Z.mod_1_r | lia]. }
assert (A8 : afact_ok E' 8 (mkAF (2 ^ 46) (2 ^ 47) 4)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U8'.
  split; [lia|]. split; [change (2 ^ 4) with 16; exact N1 | lia]. }
assert (A19 : afact_ok E' 19 (mkAF 4096 (2 ^ 47) 5)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U19'.
  split; [lia|]. split; [change (2 ^ 5) with 32; exact Hal32 | lia]. }
assert (A18 : afact_ok E' 18 (mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 0)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U18'.
  split; [unfold cno_SF, SHADOW_OFF in *; lia|]. split; [rewrite Z.pow_0_r; apply Z.mod_1_r | lia]. }
assert (HSB : st_ok tfibsegs E' ss_C1 (restrict (w_H W3) ms3)).
{ unfold ss_C1. apply st_ok_set_facts; [exact HSA|]. unfold cno_GC.
  split; [|split; [cbn; exact I|]].
  - cbn [f_atoms atoms_ok ss_C cno_ss fss_ret_s0_args ss_facts cno_gf].
    exact (conj A51 (conj A52 (conj A53 (conj A54 (conj A55 (conj A10 (conj A22
      (conj A8 (conj A19 (conj A18 I)))))))))).
  - cbn [f_alias alias_ok]. split; [|split; [|split; [|split; [|exact I]]]].
    + apply U_inj. rewrite U_SAlu, (U_atom E' 10 t ltac:(rewrite (Hold 10%nat ltac:(lia)); exact E10) ltac:(lia)),
        (U_atom E' 22 (cno_n cx) ltac:(rewrite (Hold 22%nat ltac:(lia)); exact E22) ltac:(lia)),
        (U_atom E' 51 x1 F51 ltac:(lia)).
      cbn [zalu_raw]. rewrite (zcanon_id (t + cno_n cx) ltac:(unfold M64; lia)). unfold x1. reflexivity.
    + apply U_inj. rewrite U_srl3, (U_atom E' 51 x1 F51 ltac:(lia)), (U_atom E' 52 (x1 / 8) F52 ltac:(lia)).
      reflexivity.
    + apply U_inj. rewrite U_SAlu, (U_atom E' 52 (x1 / 8) F52 ltac:(lia)),
        (U_atom E' 24 SHADOW_OFF ltac:(rewrite (Hold 24%nat ltac:(lia)); exact E24) ltac:(unfold SHADOW_OFF; lia)),
        (U_atom E' 53 (SHADOW_OFF + x1 / 8) F53 ltac:(unfold SHADOW_OFF; lia)).
      cbn [zalu_raw]. rewrite (Z.add_comm (x1 / 8) SHADOW_OFF).
      apply zcanon_id. unfold M64, SHADOW_OFF in *. lia.
    + apply U_inj. rewrite U_SAlu, (U_atom E' 10 t ltac:(rewrite (Hold 10%nat ltac:(lia)); exact E10) ltac:(lia)),
        U_SLit, (U_atom E' 55 (2 ^ 64 - 1 - t) F55 ltac:(lia)).
      cbn [zalu_raw]. change (zcanon (-1)) with (2 ^ 64 - 1). rewrite (cno_not64 t ltac:(lia)).
      apply zcanon_id. unfold M64. lia. }
pose proof HARU as HARU0.
(* ---- the common tail: the __asan_memset call, the resume at 0x813f8 and INV_S ---- *)
assert (TAIL : forall (ssF : sstate) (ms' : machine_state) (mat' : list word),
  st_ok tfibsegs E' ssF (restrict (w_H W3) ms') ->
  ss_pc ssF = PC_memset -> ss_regs ssF = ss_regs ss_MS -> ss_mem ssF = ss_mem ss_MS -> ss_resv ssF = None ->
  cno_J B cx 3 ly3 S3 W3 (unpoison (c_U cx) (ms_mem ms')) (with_vm_backing (m_vm_lazy md3) mat' md3) ->
  ARU tfibsegs B ly3 S3 (c_U cx) W3 (ms_mem ms') (with_vm_backing (m_vm_lazy md3) mat' md3) ->
  frame_of E' (ss_mem ss_C ++ [cno_RX; cno_RSH]) (ms_mem ms3) (ms_mem ms') ->
  SRr tfibsegs W3 (mkCfg ms' (with_vm_backing (m_vm_lazy md3) mat' md3)) (cno_post B cx)).
{ intros ssF ms' mat' HSF Hpc Hrg Hmm Hrv HJ' HARU' HFF.
  destruct (cno_keepX cx E' 0x813bc cno_flag_chunk cno_sl18 ly3 S3 (c_U cx) W3 (ms_mem ms3) md3 x1
    (ms_mem ms3) (ms_mem ms') Hb HARU0 Hin EF U8' U9' U19' U18' U51' HFF) as (KL & KB).
  assert (Hxfp : ~ inFP FS_PSTAT_FP x1)
    by (apply (cno_blk_offfp ly3 S3 W3 (unpoison (c_U cx) (ms_mem ms3)) md3 t (cno_n cx + 18) x1 HAR HtIn);
        rewrite Hreq; unfold x1; lia).
  assert (R1 : getr (ms_regs ms') 1 = w64 0x813f8)
    by (apply (fsw_reg_lit (w_H W3) E' ssF ms' 1%bv 0x813f8 HSF);
        [rewrite Hrg; vm_compute; reflexivity | lia]).
  assert (R10 : getr (ms_regs ms') 10 = w64 (t + cno_n cx + 1))
    by (apply (cno_reg_off (w_H W3) E' ssF ms' 10%bv 51 1 x1 HSF
         ltac:(rewrite Hrg; vm_compute; reflexivity) F51 ltac:(lia) ltac:(unfold x1; lia))).
  assert (R11 : getr (ms_regs ms') 11 = w64 0)
    by (apply (fsw_reg_lit (w_H W3) E' ssF ms' 11%bv 0 HSF); [rewrite Hrg; vm_compute; reflexivity | lia]).
  assert (R12 : getr (ms_regs ms') 12 = w64 16)
    by (apply (fsw_reg_lit (w_H W3) E' ssF ms' 12%bv 16 HSF); [rewrite Hrg; vm_compute; reflexivity | lia]).
  assert (R2 : getr (ms_regs ms') 2 = w64 (cno_sp1 cx))
    by (rewrite (cno_reg (w_H W3) E' ssF ms' 2%bv 2 HSF ltac:(rewrite Hrg; vm_compute; reflexivity));
        rewrite (Hold 2%nat ltac:(lia)); exact C2).
  assert (R8 : getr (ms_regs ms') 8 = w64 (cno_sp0 cx))
    by (rewrite (cno_reg (w_H W3) E' ssF ms' 8%bv 8 HSF ltac:(rewrite Hrg; vm_compute; reflexivity));
        rewrite (Hold 8%nat ltac:(lia)); exact C8).
  assert (R9 : getr (ms_regs ms') 9 = w64 (cno_sp1 cx))
    by (rewrite (cno_reg (w_H W3) E' ssF ms' 9%bv 9 HSF ltac:(rewrite Hrg; vm_compute; reflexivity));
        rewrite (Hold 9%nat ltac:(lia)); exact C9).
  assert (R18 : getr (ms_regs ms') 18 = w64 (cno_SF cx))
    by (rewrite (cno_reg (w_H W3) E' ssF ms' 18%bv 18 HSF ltac:(rewrite Hrg; vm_compute; reflexivity));
        rewrite (Hold 18%nat ltac:(lia)); exact C18).
  assert (R19 : getr (ms_regs ms') 19 = w64 (cno_F cx))
    by (rewrite (cno_reg (w_H W3) E' ssF ms' 19%bv 19 HSF ltac:(rewrite Hrg; vm_compute; reflexivity));
        rewrite (Hold 19%nat ltac:(lia)); exact C19).
  assert (R3 : getr (ms_regs ms') 3 = getr (c_regs cx) 3)
    by (rewrite (cno_reg (w_H W3) E' ssF ms' 3%bv 3 HSF ltac:(rewrite Hrg; vm_compute; reflexivity));
        rewrite (Hold 3%nat ltac:(lia)); exact C3).
  assert (R4 : getr (ms_regs ms') 4 = getr (c_regs cx) 4)
    by (rewrite (cno_reg (w_H W3) E' ssF ms' 4%bv 4 HSF ltac:(rewrite Hrg; vm_compute; reflexivity));
        rewrite (Hold 4%nat ltac:(lia)); exact C4).
  assert (R20 : getr (ms_regs ms') 20 = w64 b)
    by (rewrite (cno_reg (w_H W3) E' ssF ms' 20%bv 20 HSF ltac:(rewrite Hrg; vm_compute; reflexivity)); exact E20').
  assert (R21 : getr (ms_regs ms') 21 = w64 t)
    by (rewrite (cno_reg (w_H W3) E' ssF ms' 21%bv 10 HSF ltac:(rewrite Hrg; vm_compute; reflexivity));
        rewrite (Hold 10%nat ltac:(lia)); exact E10).
  assert (R22 : getr (ms_regs ms') 22 = w64 (cno_n cx + 17))
    by (apply (cno_reg_off (w_H W3) E' ssF ms' 22%bv 22 17 (cno_n cx) HSF
         ltac:(rewrite Hrg; vm_compute; reflexivity) ltac:(rewrite (Hold 22%nat ltac:(lia)); exact E22)
         ltac:(lia) ltac:(lia))).
  assert (R23 : getr (ms_regs ms') 23 = w64 (2 ^ 64 - 1 - t))
    by (rewrite (cno_reg (w_H W3) E' ssF ms' 23%bv 55 HSF ltac:(rewrite Hrg; vm_compute; reflexivity)); exact F55).
  assert (R24 : getr (ms_regs ms') 24 = w64 SHADOW_OFF)
    by (rewrite (cno_reg (w_H W3) E' ssF ms' 24%bv 24 HSF ltac:(rewrite Hrg; vm_compute; reflexivity)); exact E24').
  assert (R25 : getr (ms_regs ms') 25 = w64 (cno_F cx))
    by (rewrite (cno_reg (w_H W3) E' ssF ms' 25%bv 25 HSF ltac:(rewrite Hrg; vm_compute; reflexivity)); exact E25').
  assert (Hzt1 : zbytes_at tfibsegs W3 (ms_mem ms') t (c_db cx ++ [0])).
  { apply (cno_zb_ext0 W3 (ms_mem ms3) (ms_mem ms') t (c_db cx) (cno_n cx) Hzt ltac:(reflexivity)).
    - intros j Hj. exact (KB t (cno_n cx + 18) j HtIn ltac:(rewrite Hreq; lia) ltac:(unfold x1 in *; lia)).
    - set (rX := nth 4 (ss_mem ss_MS) (YP09.mkRegion None 0 0 0 0 [])).
      assert (HrX : nth_error (ss_mem ssF) 4 = Some rX) by (rewrite Hmm; vm_compute; reflexivity).
      assert (HcX : YP09.chunk_ok tfibsegs E' (mrestrict (w_H W3) (ms_mem ms')) (bv_unsigned (ew E' 51))
        (YP09.mkChunk 0 (CVal 1 (SLit 0))))
        by (apply (cno_chunk_at E' ssF (w_H W3) ms' 4 rX 51 (YP09.mkChunk 0 (CVal 1 (SLit 0))) HSF HrX
             ltac:(vm_compute; reflexivity) ltac:(vm_compute; tauto))).
      rewrite U51' in HcX.
      pose proof (val_of_chunk_ok tfibsegs E' (mrestrict (w_H W3) (ms_mem ms')) x1 0 1 (SLit 0) 0 HcX
        ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as HV.
      rewrite Z.add_0_r in HV. unfold x1 in HV. exact HV. }
  assert (Hza1 : zbytes_at tfibsegs W3 (ms_mem ms') a (pn_copy (c_db cx) 65)).
  { apply (cno_zb_kept W3 (ms_mem ms3) (ms_mem ms') a _ Hza).
    intros j Hj. rewrite (cno_pn_length (c_db cx) 65) in Hj.
    exact (KB a (cno_n cx + 18) j HaIn ltac:(rewrite Hreq; unfold cno_n in *; lia)
      ltac:(unfold x1, cno_n in *; lia)). }
  assert (Hzb1 : zbytes_at tfibsegs W3 (ms_mem ms') b (pn_copy (c_db cx) 66)).
  { apply (cno_zb_kept W3 (ms_mem ms3) (ms_mem ms') b _ Hzb).
    intros j Hj. rewrite (cno_pn_length (c_db cx) 66) in Hj.
    exact (KB b (cno_n cx + 18) j HbIn ltac:(rewrite Hreq; unfold cno_n in *; lia)
      ltac:(unfold x1, cno_n in *; lia)). }
  assert (Hg1 : fs_glob tfibsegs W3 (ms_mem ms') (c_live cx) (c_peak cx) (c_cnt cx) (c_fail cx)).
  { apply (cno_glob_ledger W3 W3 (ms_mem ms3) (ms_mem ms') _ _ _ _); [|exact Hg].
    intros y Hy. apply (aview_at tfibsegs (w_H W3) (ms_mem ms') (ms_mem ms3) y).
    apply KL; [exact Hy | intros Ey; apply Hxfp; rewrite <- Ey; exact Hy]. }
  assert (Hsite : cno_site B cx 3 ly3 S3 (c_U cx) W3 (ms_regs ms') (ms_mem ms')
    (with_vm_backing (m_vm_lazy md3) mat' md3))
    by exact (cno_site_of B cx E' ssF W3 ms' 3 ly3 S3 (c_U cx) _ 0x813f8 HE' U8' HSF
      ltac:(rewrite Hmm; vm_compute; reflexivity) HJ' HARU' Hh R2 R8 R3 R4 R1 ltac:(lia) ltac:(reflexivity)).
  destruct (cno_saved_of_st cx E' ssF W3 ms' HE' U8' HSF ltac:(rewrite Hmm; vm_compute; reflexivity))
    as (_ & _ & Hsvall).
  set (rF := nth 1 (ss_mem ss_MS) (YP09.mkRegion None 0 0 0 0 [])).
  set (rL := nth 3 (ss_mem ss_MS) (YP09.mkRegion None 0 0 0 0 [])).
  assert (HrF : nth_error (ss_mem ssF) 1 = Some rF) by (rewrite Hmm; vm_compute; reflexivity).
  assert (HrL : nth_error (ss_mem ssF) 3 = Some rL) by (rewrite Hmm; vm_compute; reflexivity).
  assert (HcFL : YP09.chunk_ok tfibsegs E' (mrestrict (w_H W3) (ms_mem ms')) (bv_unsigned (ew E' 19))
    (YP09.mkChunk 120 (CVal 8 (SOff 46 0))))
    by (apply (cno_chunk_at E' ssF (w_H W3) ms' 1 rF 19 (YP09.mkChunk 120 (CVal 8 (SOff 46 0))) HSF HrF
         ltac:(vm_compute; reflexivity) ltac:(vm_compute; tauto))).
  assert (HcL : YP09.chunk_ok tfibsegs E' (mrestrict (w_H W3) (ms_mem ms')) (bv_unsigned (ew E' 9))
    (YP09.mkChunk 24 (CVal 8 (SOff 48 0))))
    by (apply (cno_chunk_at E' ssF (w_H W3) ms' 3 rL 9 (YP09.mkChunk 24 (CVal 8 (SOff 48 0))) HSF HrL
         ltac:(vm_compute; reflexivity) ltac:(vm_compute; tauto))).
  rewrite U19' in HcFL. rewrite U9' in HcL.
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W3) E' ssF ms' HSF Hrv), Hpc.
  change (mkCfg (mkst (ms_regs ms') (Z_to_bv 64 PC_memset) (ms_mem ms') (seg_rom tfibsegs))
            (with_vm_backing (m_vm_lazy md3) mat' md3))
    with (cfg_at tfibsegs PC_memset (ms_regs ms') (ms_mem ms')
            (with_vm_backing (m_vm_lazy md3) mat' md3)).
  assert (Hab3 : ablocks B ly3 S3 =
    ablocks B (c_ly cx) (c_S cx) ++ [(a, cno_n cx + 18); (b, cno_n cx + 18)] ++ [(t, cno_n cx + 18)])
    by (rewrite Hab; cbn [app cno_raw]; reflexivity).
  eapply SRr_bind.
  { exact (cno_call_mset B AMEMSET cx 3 ly3 S3 (c_U cx) W3 (ms_regs ms') (ms_mem ms')
      (with_vm_backing (m_vm_lazy md3) mat' md3) t Hb Hsite eq_refl R1 R10 R11 R12
      (ex_intro _ [(a, cno_n cx + 18); (b, cno_n cx + 18)] Hab3)). }
  cbv beta. intros W' c' _ Hret.
  destruct (cno_resume B cx 3 ly3 S3 (c_U cx) W3 (ms_regs ms') (ms_mem ms')
      (with_vm_backing (m_vm_lazy md3) mat' md3) 0 (c_U cx)
      (fun y => t + cno_n cx + 1 <= y < t + cno_n cx + 17) _ W' c'
      (fs_extraT ++ cno_extra (c_regs cx) (cno_FL cx) (cno_SF cx) a b t) cno_flag_chunk cno_sl18
      Hb Hsite Hret R9 R18 R19)
    as (ly' & S' & regs' & mem' & md' & Ec & HJ2 & HARU2 & Hh2 & HP & HBK & HZ & HPP & HS2').
  - intros y Hy. lia.
  - vm_compute. reflexivity.
  - intros regs2. apply (Hsvall (Ereg regs2 (fs_extraT ++ cno_extra (c_regs cx) (cno_FL cx) (cno_SF cx) a b t))).
    intros j Hj. pose proof HE' as (_ & X33 & _).
    rewrite (X33 j Hj). destruct (cno_E_env cx regs2 a b t) as (_ & Y33 & _). exact (Y33 j Hj).
  - constructor; [|apply Forall_nil]. cbn. split; [lia|]. split; [lia|]. intros i Hi.
    destruct HxF as [HQ | HQ]; lia.
  - constructor; [|apply Forall_nil]. cbn. split; [lia|]. split; [lia|]. intros i Hi. lia.
  - intros regs2 _. constructor; [|apply Forall_nil].
    apply (cno_chunk_env E' _ _ _ _ _ _ _ HcFL). rewrite !fsw_SOff0.
    pose proof HE' as (_ & _ & Y46 & _). rewrite Y46.
    destruct (cno_E_env cx regs2 a b t) as (_ & _ & X46 & _). exact X46.
  - intros regs2 _. constructor; [|apply Forall_nil].
    apply (cno_chunk_env E' _ _ _ _ _ _ _ HcL). rewrite !fsw_SOff0, E48'.
    change 48%nat with (32 + 16)%nat. rewrite ew_Ereg_extra. reflexivity.
  - cbv beta in HPP. destruct HPP as (Ely & ES & EW & P10 & Pz & Pkeep & Prad).
    subst ly' S' W'.
    assert (Era : raZ (ms_regs ms') = 0x813f8)
      by (unfold raZ; rewrite R1; unfold w64; apply wz; lia).
    rewrite Era in Ec, HS2'. subst c'.
    set (E2 := Ereg regs' (fs_extraT ++ cno_extra (c_regs cx) (cno_FL cx) (cno_SF cx) a b t)) in *.
    assert (KR : forall (r : bv 5) n, Z.of_nat n = bv_unsigned r -> acallee_saved (bv_unsigned r) ->
      ew E2 n = getr (ms_regs ms') r).
    { intros r n Hn' Hc. subst E2. rewrite (ew_Ereg_nat regs' _ n r Hn'). exact (fsw_pres _ _ r HP Hc). }
    apply (HNX cx E2 3 ly3 S3 (c_U cx) W3 (mkst regs' (Z_to_bv 64 0x813f8) mem' (seg_rom tfibsegs)) md' Hb
      (cno_E_env cx regs' a b t) HJ2 HARU2).
    + exists a, b, t. split; [reflexivity|]. split; [reflexivity|].
      split; [exact Hab|]. split; [exact Hh2|].
      split; [unfold cno_core; rewrite (KR 2%bv 2%nat eq_refl ltac:(cno_cs)), (KR 8%bv 8%nat eq_refl ltac:(cno_cs)),
        (KR 9%bv 9%nat eq_refl ltac:(cno_cs)), (KR 18%bv 18%nat eq_refl ltac:(cno_cs)),
        (KR 19%bv 19%nat eq_refl ltac:(cno_cs)), (KR 3%bv 3%nat eq_refl ltac:(cno_cs)),
        (KR 4%bv 4%nat eq_refl ltac:(cno_cs)); repeat split; assumption|].
      split; [subst E2; rewrite (ew_Ereg_nat regs' _ 10 10%bv eq_refl); exact P10|].
      split; [rewrite (KR 20%bv 20%nat eq_refl ltac:(cno_cs)); exact R20|].
      split; [rewrite (KR 21%bv 21%nat eq_refl ltac:(cno_cs)); exact R21|].
      split; [rewrite (KR 22%bv 22%nat eq_refl ltac:(cno_cs)); exact R22|].
      split; [rewrite (KR 23%bv 23%nat eq_refl ltac:(cno_cs)); exact R23|].
      split; [rewrite (KR 24%bv 24%nat eq_refl ltac:(cno_cs)); exact R24|].
      split; [rewrite (KR 25%bv 25%nat eq_refl ltac:(cno_cs)); exact R25|].
      split; [subst E2; change 48%nat with (32 + 16)%nat; rewrite ew_Ereg_extra; reflexivity|].
      split; [subst E2; change 49%nat with (32 + 17)%nat; rewrite ew_Ereg_extra; reflexivity|].
      split; [subst E2; change 50%nat with (32 + 18)%nat; rewrite ew_Ereg_extra; reflexivity|].
      cbn [ms_mem mkst].
      split.
      { apply (cno_zbytes_kept W3 W3 (ms_mem ms') mem' a (pn_copy (c_db cx) 65)); [|exact Hza1].
        intros j Hj. rewrite (cno_pn_length (c_db cx) 65) in Hj.
        apply (HBK a (cno_n cx + 18) j HaIn HaIn ltac:(rewrite Hreq; unfold cno_n in *; lia)).
        unfold cno_n in *. lia. }
      split.
      { apply (cno_zbytes_kept W3 W3 (ms_mem ms') mem' b (pn_copy (c_db cx) 66)); [|exact Hzb1].
        intros j Hj. rewrite (cno_pn_length (c_db cx) 66) in Hj.
        apply (HBK b (cno_n cx + 18) j HbIn HbIn ltac:(rewrite Hreq; unfold cno_n in *; lia)).
        unfold cno_n in *. lia. }
      split.
      { assert (Esplit : c_db cx ++ repeat 0 17%nat = (c_db cx ++ [0]) ++ repeat 0 16%nat).
        { rewrite <- app_assoc. f_equal.
          all: try (replace 17%nat with (1 + 16)%nat by lia; rewrite repeat_app; reflexivity). }
        rewrite Esplit. apply cno_zb_app.
        - apply (cno_zbytes_kept W3 W3 (ms_mem ms') mem' t (c_db cx ++ [0])); [|exact Hzt1].
          intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
          apply (HBK t (cno_n cx + 18) j HtIn HtIn ltac:(rewrite Hreq; unfold cno_n in *; lia)).
          unfold cno_n in *. lia.
        - rewrite length_app. cbn [length].
          replace (t + Z.of_nat (length (c_db cx) + 1)) with (t + cno_n cx + 1) by (unfold cno_n; lia).
          exact Pz. }
      split; [exact Prad|].
      apply (cno_glob_ledger W3 W3 (ms_mem ms') mem' _ _ _ _); [|exact Hg1].
      intros y Hy. apply Pkeep.
      * pose proof (fs_segs_low y (cno_pstat_img y Hy)). unfold kLowMemEnd in *. lia.
      * intros HQ.
        exact (cno_blk_offfp ly3 S3 W3 (unpoison (c_U cx) (ms_mem ms3)) md3 t (cno_n cx + 18) y HAR HtIn
          ltac:(rewrite Hreq; lia) Hy).
      * intros HQ. pose proof (cno_pstat_bounds y Hy). unfold ESTACK in HQ. lia.
    + exact HS2'. }
(* ---- the two arms of the inline check 0x813c8-0x813d4 ---- *)
destruct (Z.eq_dec sv 0) as [Hsv0 | Hsv0].
- assert (HSC : st_ok tfibsegs E' (add_cond ss_C1 (mkAC BC_EQ (SOff 54 0) (SLit 0))) (restrict (w_H W3) ms3)).
  { change (mkAC BC_EQ (SOff 54 0) (SLit 0)) with (mkAC (neg_bc BC_NE) (SOff 54 0) (SLit 0)).
    apply (st_ok_add_cond_neg tfibsegs E' ss_C1 _ BC_NE (SOff 54 0) (SLit 0) HSB).
    rewrite branch_ne_U, (U_atom E' 54 sv F54 ltac:(lia)), U_SLit, Hsv0. vm_compute. reflexivity. }
  fsw_aj_run_toU cno_tbl_ok HSC HJ HARU PC_memset.
  { change (ss_mem (add_cond ss_C1 (mkAC BC_EQ (SOff 54 0) (SLit 0))))
      with (ss_mem ss_C ++ [cno_RX; cno_RSH]).
    apply awr_ok_app.
    - eapply (cno_awr_ss B E' _ _ _ _ _ ly3 _ (c_fpos cx) (cno_F cx) (cno_sp1 cx) 0x813bc cno_flag_chunk
        cno_sl18 U8' U19' U18' U9' (eq_sym EFa)); lia.
    - eapply (awr_ok_cons_gen tfibsegs B E' cno_RX [cno_RSH] _ _ _ _ _ _ _ _ 51%nat x1);
        [reflexivity | exact U51' | | apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]].
      intros y Hy. cbn [YP09.r_wlo YP09.r_whi cno_RX] in Hy.
      left. right. right. left. exists t, (cno_n cx + 18).
      split; [exact HtIn|]. split; [exact HtNot|]. rewrite Hreq. unfold x1 in *. lia. }
  eapply (TAIL _ ms mat);
    [exact HSC | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
     | vm_compute; reflexivity | exact HJ | exact HARU | exact HF].
- assert (HSC : st_ok tfibsegs E'
    (add_cond (add_cond ss_C1 (mkAC BC_NE (SOff 54 0) (SLit 0)))
       (mkAC BC_LT (SAlu ALU_AND (SOff 51 0) (SLit 7)) (SOff 54 0))) (restrict (w_H W3) ms3)).
  { apply (st_ok_add_cond tfibsegs E' _ _ BC_LT (SAlu ALU_AND (SOff 51 0) (SLit 7)) (SOff 54 0)).
    - apply (st_ok_add_cond tfibsegs E' ss_C1 _ BC_NE (SOff 54 0) (SLit 0) HSB).
      rewrite branch_ne_U, (U_atom E' 54 sv F54 ltac:(lia)), U_SLit.
      change (zcanon 0) with 0. destruct (Z.eqb_spec sv 0) as [Hz | Hz]; [destruct (Hsv0 Hz) | reflexivity].
    - assert (Hlt : x1 mod 8 < sv).
      { unfold saddr_ok in Hsaddr. destruct Hsaddr as [Hz | (Q1 & Q2)]; [destruct (Hsv0 Hz) | exact Q1]. }
      pose proof (Z.mod_pos_bound x1 8 ltac:(lia)) as Hmb.
      assert (UA : U E' (SAlu ALU_AND (SOff 51 0) (SLit 7)) = x1 mod 8).
      { rewrite U_and_lit by lia. rewrite (U_atom E' 51 x1 F51 ltac:(lia)). apply cno_land7. lia. }
      assert (UB : U E' (SOff 54 0) = sv) by exact (U_atom E' 54 sv F54 ltac:(lia)).
      unfold U in UA, UB.
      cbn [branch_taken]. rewrite bv_lts_signed.
      rewrite (signed_of_small _ ltac:(rewrite UA; unfold half64; lia)),
              (signed_of_small _ ltac:(rewrite UB; unfold half64; lia)).
      rewrite UA, UB. apply Z.ltb_lt. lia. }
  fsw_aj_run_toU cno_tbl_ok HSC HJ HARU PC_memset.
  { change (ss_mem (add_cond (add_cond ss_C1 (mkAC BC_NE (SOff 54 0) (SLit 0)))
              (mkAC BC_LT (SAlu ALU_AND (SOff 51 0) (SLit 7)) (SOff 54 0))))
      with (ss_mem ss_C ++ [cno_RX; cno_RSH]).
    apply awr_ok_app.
    - eapply (cno_awr_ss B E' _ _ _ _ _ ly3 _ (c_fpos cx) (cno_F cx) (cno_sp1 cx) 0x813bc cno_flag_chunk
        cno_sl18 U8' U19' U18' U9' (eq_sym EFa)); lia.
    - eapply (awr_ok_cons_gen tfibsegs B E' cno_RX [cno_RSH] _ _ _ _ _ _ _ _ 51%nat x1);
        [reflexivity | exact U51' | | apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]].
      intros y Hy. cbn [YP09.r_wlo YP09.r_whi cno_RX] in Hy.
      left. right. right. left. exists t, (cno_n cx + 18).
      split; [exact HtIn|]. split; [exact HtNot|]. rewrite Hreq. unfold x1 in *. lia. }
  eapply (TAIL _ ms mat);
    [exact HSC | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
     | vm_compute; reflexivity | exact HJ | exact HARU | exact HF].
Qed.

(* ---- 0x813a0 -> 0x813bc: `beqz a0` (the abort block is not reached: t <> 0 and 4096 <= t), `mv s5,a0`, and
   `beqz s6` with its two arms (n = 0 skips the copy; n > 0 calls __asan_memcpy, ra 0x813bc) ---- *)
Lemma cno_seg_M1 : cno_from B ss_C INV_C -> cno_from B ss_M (INV_M B).
Proof.
intros HNX cx E k ly3 S3 U3 W3 ms3 md3 Hb HE HJ HARU HINV HS.
destruct HINV as (a & b & t & -> & -> & Hab & Ha0 & Ha16 & Hb0 & Hb16 & Ht0 & Hcore & E48 & E49 & E50 & E10 & E20
  & E22 & E23 & E24 & E25 & Hza & Hzb & Hrad & Hg & Hh).
pose proof (cno_nums B cx Hb) as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
pose proof asan_consts as (CA1 & CA2 & CA3 & CA4 & CA5). pose proof cno_stk as FS.
pose proof Hb as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HnM & _).
unfold PRESET_FILE_MAX_BYTES in HnM.
assert (Hn0 : 0 <= cno_n cx) by (unfold cno_n; lia).
pose proof Hcore as (C2 & C8 & C9 & C18 & C19 & C3 & C4).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _).
assert (Hin : In (1, c_fpos cx) (frames S3)) by (rewrite Hfrs; left; reflexivity).
assert (EF : ly_F ly3 = ly_F (c_ly cx)) by (destruct Hly as (_ & _ & _ & _ & _ & X & _); exact X).
assert (EFa : frame_addr ly3 1 (c_fpos cx) = cno_F cx) by (unfold cno_F, frame_addr; rewrite EF; reflexivity).
destruct (frames_bounds tfibsegs B LAWS ly3 S3 W3 (unpoison (c_U cx) (ms_mem ms3)) md3 1 (c_fpos cx) HAR Hin)
  as (HF4096 & HFceil & HFapp).
rewrite EFa in HF4096, HFceil, HFapp. change (fs_frame_bytes 1) with 128 in HF4096, HFceil, HFapp.
destruct (al_frames _ _ LAWS ly3 S3 W3 (unpoison (c_U cx) (ms_mem ms3)) md3 1 (c_fpos cx) HAR Hin)
  as (Hal32 & _ & _ & _).
rewrite EFa in Hal32.
assert (HF64 : 0 <= cno_F cx < 2 ^ 64) by (unfold in_app, kLowShadowBeg, ASAN_CEIL in HFapp; lia).
pose proof (shadow_addr_bounds (cno_F cx) ltac:(unfold kHighMemEnd; lia)) as (Hs1 & Hs2).
unfold kLowMemEnd, kHighShadowEnd in Hs1, Hs2.
destruct (cno_tfacts cx ly3 S3 W3 (ms_mem ms3) md3 a b t Hb HAR Hab)
  as (Hreq & HtIn & HtNot & Ht4096 & Htc & Htapp & Htp & HaIn & HbIn & Ha4096 & Hac & Hb4096 & Hbc & Hat & Hbt & Hd0).
assert (U8 : bv_unsigned (ew E 8) = cno_sp0 cx) by (rewrite C8; unfold w64; apply wz; lia).
assert (U9 : bv_unsigned (ew E 9) = cno_sp1 cx) by (rewrite C9; unfold w64; apply wz; lia).
assert (U19 : bv_unsigned (ew E 19) = cno_F cx) by (rewrite C19; unfold w64; apply wz; lia).
assert (U18 : bv_unsigned (ew E 18) = cno_SF cx)
  by (rewrite C18; unfold w64; apply wz; unfold cno_SF in *; lia).
assert (U10 : bv_unsigned (ew E 10) = t) by (rewrite E10; unfold w64; apply wz; lia).
assert (U22 : bv_unsigned (ew E 22) = cno_n cx) by (rewrite E22; unfold w64; apply wz; lia).
(* the two atom facts the engine needs at 0x813a0 (`beqz a0`) and 0x813a8 (`beqz s6`) *)
assert (A10 : afact_ok E 10 (mkAF 4096 (2 ^ 47) 0)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U10.
  split; [lia|]. split; [rewrite Z.pow_0_r; apply Z.mod_1_r | lia]. }
assert (A22 : afact_ok E 22 (mkAF 0 PRESET_FILE_MAX_BYTES 0)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U22.
  split; [unfold PRESET_FILE_MAX_BYTES; lia|]. split; [rewrite Z.pow_0_r; apply Z.mod_1_r | lia]. }
assert (A8 : afact_ok E 8 (mkAF (2 ^ 46) (2 ^ 47) 4)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U8.
  split; [lia|]. split; [change (2 ^ 4) with 16; exact N1 | lia]. }
assert (A19 : afact_ok E 19 (mkAF 4096 (2 ^ 47) 5)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U19.
  split; [lia|]. split; [change (2 ^ 5) with 32; exact Hal32 | lia]. }
assert (A18 : afact_ok E 18 (mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 0)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U18.
  split; [unfold cno_SF, SHADOW_OFF in *; lia|]. split; [rewrite Z.pow_0_r; apply Z.mod_1_r | lia]. }
assert (Efacts : facts_ok E (ss_facts ss_C)).
{ cbn [ss_facts ss_C cno_ss fss_ret_s0_args cno_gf f_atoms atoms_ok f_conds conds_ok f_alias alias_ok].
  exact (conj (conj A8 (conj A19 (conj A18 I))) (conj I I)). }
assert (HSB : st_ok tfibsegs E ss_M1 (restrict (w_H W3) ms3)).
{ unfold ss_M1. apply st_ok_set_facts; [exact HS|]. unfold cno_GM.
  split; [|split; [cbn; exact I | cbn; exact I]].
  cbn [f_atoms atoms_ok ss_M cno_ss fss_ret_s0_args ss_facts cno_gf].
  exact (conj A10 (conj A22 (conj A8 (conj A19 (conj A18 I))))). }
pose proof HARU as HARU0.
(* the two arms of 0x813a8 `beqz s6` *)
destruct (Z.eq_dec (cno_n cx) 0) as [Hnz | Hnz].
- (* n = 0: the copy is skipped; nothing is written between 0x813a0 and 0x813bc *)
  assert (HSC : st_ok tfibsegs E (add_cond ss_M1 (mkAC BC_EQ (SOff 22 0) (SLit 0))) (restrict (w_H W3) ms3)).
  { apply (st_ok_add_cond tfibsegs E ss_M1 _ BC_EQ (SOff 22 0) (SLit 0) HSB).
    rewrite branch_eq_U, (U_atom E 22 (cno_n cx) E22 ltac:(lia)), U_SLit, Hnz. vm_compute. reflexivity. }
  fsw_aj_run_toU cno_tbl_ok HSC HJ HARU 0x813bc.
  { eapply (cno_awr_ss B E _ _ _ _ _ ly3 _ (c_fpos cx) (cno_F cx) (cno_sp1 cx) 0x813a0 cno_flag_chunk
      cno_sl18 U8 U19 U18 U9 (eq_sym EFa)); lia. }
  destruct (cno_run_keeps B cx E 0x813a0 cno_flag_chunk cno_sl18 ly3 S3 (c_U cx) W3 (ms_mem ms3) md3
    (ms_mem ms3) (ms_mem ms) Hb HARU0 Hin EF U8 U9 U19 U18 HF) as (KL & KB).
  assert (Hza1 : zbytes_at tfibsegs W3 (ms_mem ms) a (pn_copy (c_db cx) 65)).
  { apply (cno_zb_kept W3 (ms_mem ms3) (ms_mem ms) a _ Hza).
    intros j Hj. rewrite (cno_pn_length (c_db cx) 65) in Hj.
    exact (KB a (cno_n cx + 18) j HaIn ltac:(rewrite Hreq; unfold cno_n in *; lia)). }
  assert (Hzb1 : zbytes_at tfibsegs W3 (ms_mem ms) b (pn_copy (c_db cx) 66)).
  { apply (cno_zb_kept W3 (ms_mem ms3) (ms_mem ms) b _ Hzb).
    intros j Hj. rewrite (cno_pn_length (c_db cx) 66) in Hj.
    exact (KB b (cno_n cx + 18) j HbIn ltac:(rewrite Hreq; unfold cno_n in *; lia)). }
  assert (Hrad1 : range_addressable (aview tfibsegs (w_H W3) (ms_mem ms)) SHADOW_OFF t (cno_n cx + 18)).
  { apply (cno_rad_kept W3 W3 (ms_mem ms3) (ms_mem ms) t (cno_n cx + 18) Hrad).
    intros x Hx. apply (aview_at tfibsegs (w_H W3) (ms_mem ms) (ms_mem ms3) (SHADOW_OFF + x / 8)).
    apply HF. rewrite (wz (SHADOW_OFF + x / 8) ltac:(unfold SHADOW_OFF; Z.div_mod_to_equations; lia)).
    intros Hw.
    apply (cno_zone_blksh cx ly3 S3 (c_U cx) W3 (ms_mem ms3) md3 t (cno_n cx + 18) (x - t) Hb HARU0 Hin EF HtIn
      ltac:(rewrite Hreq; lia)).
    replace (t + (x - t)) with x by lia.
    exact (cno_wr_zone cx E 0x813a0 cno_flag_chunk cno_sl18 _ U8 U9 U19 U18 Hw). }
  assert (Hg1 : fs_glob tfibsegs W3 (ms_mem ms) (c_live cx) (c_peak cx) (c_cnt cx) (c_fail cx)).
  { apply (cno_glob_ledger W3 W3 (ms_mem ms3) (ms_mem ms) _ _ _ _); [|exact Hg].
    intros y Hy. exact (aview_at tfibsegs (w_H W3) (ms_mem ms) (ms_mem ms3) y (KL y Hy)). }
  assert (Hzt1 : zbytes_at tfibsegs W3 (ms_mem ms) t (c_db cx)).
  { intros j Hj. assert (length (c_db cx) = 0%nat) by (unfold cno_n in Hnz; lia). lia. }
  pose proof (st_ok_set_facts tfibsegs E _ _ (ss_facts ss_C) HSC Efacts) as HX.
  apply (HNX cx E 3 ly3 S3 (c_U cx) W3 ms (with_vm_backing (m_vm_lazy md3) mat md3) Hb HE HJ HARU).
  + exists a, b, t. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hab|]. split; [exact Hh|].
    split; [exact Hcore|]. split; [exact E10|]. split; [exact E20|]. split; [exact E22|].
    split; [exact E24|]. split; [exact E25|]. split; [exact E48|]. split; [exact E49|]. split; [exact E50|].
    split; [exact Hza1|]. split; [exact Hzb1|]. split; [exact Hzt1|]. split; [exact Hrad1 | exact Hg1].
  + lazymatch type of HX with st_ok _ _ ?ss _ => replace ss_C with ss by (vm_compute; reflexivity) end.
    exact HX.
- (* n > 0: __asan_memcpy (t, d, n) at 0x813b8 *)
  assert (HSC : st_ok tfibsegs E (add_cond ss_M1 (mkAC BC_NE (SOff 22 0) (SLit 0))) (restrict (w_H W3) ms3)).
  { change (mkAC BC_NE (SOff 22 0) (SLit 0)) with (mkAC (neg_bc BC_EQ) (SOff 22 0) (SLit 0)).
    apply (st_ok_add_cond_neg tfibsegs E ss_M1 _ BC_EQ (SOff 22 0) (SLit 0) HSB).
    rewrite branch_eq_U, (U_atom E 22 (cno_n cx) E22 ltac:(lia)), U_SLit.
    change (zcanon 0) with 0. destruct (Z.eqb_spec (cno_n cx) 0) as [Hq | Hq]; [destruct (Hnz Hq) | reflexivity]. }
  fsw_aj_run_toU cno_tbl_ok HSC HJ HARU PC_memcpy.
  { eapply (cno_awr_ss B E _ _ _ _ _ ly3 _ (c_fpos cx) (cno_F cx) (cno_sp1 cx) 0x813a0 cno_flag_chunk
      cno_sl18 U8 U19 U18 U9 (eq_sym EFa)); lia. }
  destruct (cno_run_keeps B cx E 0x813a0 cno_flag_chunk cno_sl18 ly3 S3 (c_U cx) W3 (ms_mem ms3) md3
    (ms_mem ms3) (ms_mem ms) Hb HARU0 Hin EF U8 U9 U19 U18 HF) as (KL & KB).
  assert (Hza1 : zbytes_at tfibsegs W3 (ms_mem ms) a (pn_copy (c_db cx) 65)).
  { apply (cno_zb_kept W3 (ms_mem ms3) (ms_mem ms) a _ Hza).
    intros j Hj. rewrite (cno_pn_length (c_db cx) 65) in Hj.
    exact (KB a (cno_n cx + 18) j HaIn ltac:(rewrite Hreq; unfold cno_n in *; lia)). }
  assert (Hzb1 : zbytes_at tfibsegs W3 (ms_mem ms) b (pn_copy (c_db cx) 66)).
  { apply (cno_zb_kept W3 (ms_mem ms3) (ms_mem ms) b _ Hzb).
    intros j Hj. rewrite (cno_pn_length (c_db cx) 66) in Hj.
    exact (KB b (cno_n cx + 18) j HbIn ltac:(rewrite Hreq; unfold cno_n in *; lia)). }
  assert (Hrad1 : range_addressable (aview tfibsegs (w_H W3) (ms_mem ms)) SHADOW_OFF t (cno_n cx + 18)).
  { apply (cno_rad_kept W3 W3 (ms_mem ms3) (ms_mem ms) t (cno_n cx + 18) Hrad).
    intros x Hx. apply (aview_at tfibsegs (w_H W3) (ms_mem ms) (ms_mem ms3) (SHADOW_OFF + x / 8)).
    apply HF. rewrite (wz (SHADOW_OFF + x / 8) ltac:(unfold SHADOW_OFF; Z.div_mod_to_equations; lia)).
    intros Hw.
    apply (cno_zone_blksh cx ly3 S3 (c_U cx) W3 (ms_mem ms3) md3 t (cno_n cx + 18) (x - t) Hb HARU0 Hin EF HtIn
      ltac:(rewrite Hreq; lia)).
    replace (t + (x - t)) with x by lia.
    exact (cno_wr_zone cx E 0x813a0 cno_flag_chunk cno_sl18 _ U8 U9 U19 U18 Hw). }
  assert (Hg1 : fs_glob tfibsegs W3 (ms_mem ms) (c_live cx) (c_peak cx) (c_cnt cx) (c_fail cx)).
  { apply (cno_glob_ledger W3 W3 (ms_mem ms3) (ms_mem ms) _ _ _ _); [|exact Hg].
    intros y Hy. exact (aview_at tfibsegs (w_H W3) (ms_mem ms) (ms_mem ms3) y (KL y Hy)). }
  lazymatch type of HSC with st_ok _ _ ?ss _ => set (ssA := ss) in HSC end.
  assert (R1 : getr (ms_regs ms) 1 = w64 0x813bc)
    by (apply (fsw_reg_lit (w_H W3) E ssA ms 1%bv 0x813bc HSC); [vm_compute; reflexivity | lia]).
  assert (R10 : getr (ms_regs ms) 10 = w64 t)
    by (rewrite (cno_reg (w_H W3) E ssA ms 10%bv 10 HSC ltac:(vm_compute; reflexivity)); exact E10).
  assert (R11 : getr (ms_regs ms) 11 = w64 (c_d cx))
    by (rewrite (cno_reg (w_H W3) E ssA ms 11%bv 23 HSC ltac:(vm_compute; reflexivity)); exact E23).
  assert (R12 : getr (ms_regs ms) 12 = w64 (cno_n cx))
    by (rewrite (cno_reg (w_H W3) E ssA ms 12%bv 22 HSC ltac:(vm_compute; reflexivity)); exact E22).
  assert (R2 : getr (ms_regs ms) 2 = w64 (cno_sp1 cx))
    by (rewrite (cno_reg (w_H W3) E ssA ms 2%bv 2 HSC ltac:(vm_compute; reflexivity)); exact C2).
  assert (R8 : getr (ms_regs ms) 8 = w64 (cno_sp0 cx))
    by (rewrite (cno_reg (w_H W3) E ssA ms 8%bv 8 HSC ltac:(vm_compute; reflexivity)); exact C8).
  assert (R9 : getr (ms_regs ms) 9 = w64 (cno_sp1 cx))
    by (rewrite (cno_reg (w_H W3) E ssA ms 9%bv 9 HSC ltac:(vm_compute; reflexivity)); exact C9).
  assert (R18 : getr (ms_regs ms) 18 = w64 (cno_SF cx))
    by (rewrite (cno_reg (w_H W3) E ssA ms 18%bv 18 HSC ltac:(vm_compute; reflexivity)); exact C18).
  assert (R19 : getr (ms_regs ms) 19 = w64 (cno_F cx))
    by (rewrite (cno_reg (w_H W3) E ssA ms 19%bv 19 HSC ltac:(vm_compute; reflexivity)); exact C19).
  assert (R3 : getr (ms_regs ms) 3 = getr (c_regs cx) 3)
    by (rewrite (cno_reg (w_H W3) E ssA ms 3%bv 3 HSC ltac:(vm_compute; reflexivity)); exact C3).
  assert (R4 : getr (ms_regs ms) 4 = getr (c_regs cx) 4)
    by (rewrite (cno_reg (w_H W3) E ssA ms 4%bv 4 HSC ltac:(vm_compute; reflexivity)); exact C4).
  assert (R20 : getr (ms_regs ms) 20 = w64 b)
    by (rewrite (cno_reg (w_H W3) E ssA ms 20%bv 20 HSC ltac:(vm_compute; reflexivity)); exact E20).
  assert (R21 : getr (ms_regs ms) 21 = w64 t)
    by (rewrite (cno_reg (w_H W3) E ssA ms 21%bv 10 HSC ltac:(vm_compute; reflexivity)); exact E10).
  assert (R22 : getr (ms_regs ms) 22 = w64 (cno_n cx))
    by (rewrite (cno_reg (w_H W3) E ssA ms 22%bv 22 HSC ltac:(vm_compute; reflexivity)); exact E22).
  assert (R24 : getr (ms_regs ms) 24 = w64 SHADOW_OFF)
    by (rewrite (cno_reg (w_H W3) E ssA ms 24%bv 24 HSC ltac:(vm_compute; reflexivity)); exact E24).
  assert (R25 : getr (ms_regs ms) 25 = w64 (cno_F cx))
    by (rewrite (cno_reg (w_H W3) E ssA ms 25%bv 25 HSC ltac:(vm_compute; reflexivity)); exact E25).
  assert (Hsite : cno_site B cx 3 ly3 S3 (c_U cx) W3 (ms_regs ms) (ms_mem ms)
    (with_vm_backing (m_vm_lazy md3) mat md3))
    by exact (cno_site_of B cx E ssA W3 ms 3 ly3 S3 (c_U cx) _ 0x813bc HE U8 HSC
      ltac:(vm_compute; reflexivity) HJ HARU Hh R2 R8 R3 R4 R1 ltac:(lia) ltac:(reflexivity)).
  destruct (cno_saved_of_st cx E ssA W3 ms HE U8 HSC ltac:(vm_compute; reflexivity)) as (_ & _ & Hsvall).
  set (rF := nth 1 (ss_mem ssA) (YP09.mkRegion None 0 0 0 0 [])).
  set (rL := nth 3 (ss_mem ssA) (YP09.mkRegion None 0 0 0 0 [])).
  assert (HcFL : YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms)) (bv_unsigned (ew E 19))
    (YP09.mkChunk 120 (CVal 8 (SOff 46 0))))
    by (apply (cno_chunk_at E ssA (w_H W3) ms 1 rF 19 (YP09.mkChunk 120 (CVal 8 (SOff 46 0))) HSC
         ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; tauto))).
  assert (HcL : YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms)) (bv_unsigned (ew E 9))
    (YP09.mkChunk 24 (CVal 8 (SOff 48 0))))
    by (apply (cno_chunk_at E ssA (w_H W3) ms 3 rL 9 (YP09.mkChunk 24 (CVal 8 (SOff 48 0))) HSC
         ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; tauto))).
  rewrite U19 in HcFL. rewrite U9 in HcL.
  assert (Hab3 : ablocks B ly3 S3 =
    ablocks B (c_ly cx) (c_S cx) ++ [(a, cno_n cx + 18); (b, cno_n cx + 18)] ++ [(t, cno_n cx + 18)])
    by (rewrite Hab; cbn [app cno_raw]; reflexivity).
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W3) E ssA ms HSC ltac:(vm_compute; reflexivity)).
  replace (ss_pc ssA) with PC_memcpy by (vm_compute; reflexivity).
  change (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 PC_memcpy) (ms_mem ms) (seg_rom tfibsegs))
            (with_vm_backing (m_vm_lazy md3) mat md3))
    with (cfg_at tfibsegs PC_memcpy (ms_regs ms) (ms_mem ms) (with_vm_backing (m_vm_lazy md3) mat md3)).
  eapply SRr_bind.
  { exact (cno_call_mcpy B AMEMCPY cx 3 ly3 S3 (c_U cx) W3 (ms_regs ms) (ms_mem ms)
      (with_vm_backing (m_vm_lazy md3) mat md3) t Hb Hsite eq_refl R1 R10 R11 R12 ltac:(lia)
      (ex_intro _ [(a, cno_n cx + 18); (b, cno_n cx + 18)] Hab3)). }
  cbv beta. intros W' c' _ Hret.
  destruct (cno_resume B cx 3 ly3 S3 (c_U cx) W3 (ms_regs ms) (ms_mem ms)
      (with_vm_backing (m_vm_lazy md3) mat md3) 0 (c_U cx) (fun y => t <= y < t + cno_n cx) _ W' c'
      (fs_extraT ++ cno_extra (c_regs cx) (cno_FL cx) (cno_SF cx) a b t) cno_flag_chunk cno_sl18
      Hb Hsite Hret R9 R18 R19)
    as (ly' & S' & regs' & mem' & md' & Ec & HJ2 & HARU2 & Hh2 & HP & HBK & HZ & HPP & HS2').
  + intros y Hy. lia.
  + vm_compute. reflexivity.
  + intros regs2. apply (Hsvall (Ereg regs2 (fs_extraT ++ cno_extra (c_regs cx) (cno_FL cx) (cno_SF cx) a b t))).
    intros j Hj. pose proof HE as (_ & X33 & _).
    rewrite (X33 j Hj). destruct (cno_E_env cx regs2 a b t) as (_ & Y33 & _). exact (Y33 j Hj).
  + constructor; [|apply Forall_nil]. cbn. split; [lia|]. split; [lia|]. intros i Hi.
    pose proof (sep_block_frame tfibsegs B LAWS ly3 S3 W3 (unpoison (c_U cx) (ms_mem ms3)) md3 t
      (cno_n cx + 18) 1 (c_fpos cx) HAR HtIn Hin) as Hd.
    rewrite EFa in Hd. change (fs_frame_bytes 1) with 128 in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
    rewrite Hreq in Hd. lia.
  + constructor; [|apply Forall_nil]. cbn. split; [lia|]. split; [lia|]. intros i Hi. lia.
  + intros regs2 _. constructor; [|apply Forall_nil].
    apply (cno_chunk_env E _ _ _ _ _ _ _ HcFL). rewrite !fsw_SOff0.
    pose proof HE as (_ & _ & Y46 & _). rewrite Y46.
    destruct (cno_E_env cx regs2 a b t) as (_ & _ & X46 & _). exact X46.
  + intros regs2 _. constructor; [|apply Forall_nil].
    apply (cno_chunk_env E _ _ _ _ _ _ _ HcL). rewrite !fsw_SOff0, E48.
    change 48%nat with (32 + 16)%nat. rewrite ew_Ereg_extra. reflexivity.
  + cbv beta in HPP. destruct HPP as (Ely & ES & EW & P10 & Pzt & Pkeep).
    subst ly' S' W'.
    assert (Era : raZ (ms_regs ms) = 0x813bc) by (unfold raZ; rewrite R1; unfold w64; apply wz; lia).
    rewrite Era in Ec, HS2'. subst c'.
    set (E2 := Ereg regs' (fs_extraT ++ cno_extra (c_regs cx) (cno_FL cx) (cno_SF cx) a b t)) in *.
    assert (KR : forall (r : bv 5) n, Z.of_nat n = bv_unsigned r -> acallee_saved (bv_unsigned r) ->
      ew E2 n = getr (ms_regs ms) r).
    { intros r n Hn' Hc. subst E2. rewrite (ew_Ereg_nat regs' _ n r Hn'). exact (fsw_pres _ _ r HP Hc). }
    assert (E210 : ew E2 10 = w64 t)
      by (subst E2; rewrite (ew_Ereg_nat regs' _ 10 10%bv eq_refl); exact P10).
    assert (HSC2 : st_ok tfibsegs E2 ss_C
      (restrict (w_H W3) (mkst regs' (Z_to_bv 64 0x813bc) mem' (seg_rom tfibsegs)))).
    { apply (st_ok_set_reg tfibsegs E2 _ _ 21%bv (SOff 10 0) HS2').
      - cbn. discriminate.
      - cbn [ms_regs mkst]. rewrite fsw_SOff0, E210.
        rewrite (fsw_pres (ms_regs ms) regs' 21%bv HP ltac:(cno_cs)). exact R21. }
    apply (HNX cx E2 3 ly3 S3 (c_U cx) W3 (mkst regs' (Z_to_bv 64 0x813bc) mem' (seg_rom tfibsegs)) md' Hb
      (cno_E_env cx regs' a b t) HJ2 HARU2).
    * exists a, b, t. split; [reflexivity|]. split; [reflexivity|].
      split; [exact Hab|]. split; [exact Hh2|].
      split; [unfold cno_core; rewrite (KR 2%bv 2%nat eq_refl ltac:(cno_cs)), (KR 8%bv 8%nat eq_refl ltac:(cno_cs)),
        (KR 9%bv 9%nat eq_refl ltac:(cno_cs)), (KR 18%bv 18%nat eq_refl ltac:(cno_cs)),
        (KR 19%bv 19%nat eq_refl ltac:(cno_cs)), (KR 3%bv 3%nat eq_refl ltac:(cno_cs)),
        (KR 4%bv 4%nat eq_refl ltac:(cno_cs)); repeat split; assumption|].
      split; [exact E210|].
      split; [rewrite (KR 20%bv 20%nat eq_refl ltac:(cno_cs)); exact R20|].
      split; [rewrite (KR 22%bv 22%nat eq_refl ltac:(cno_cs)); exact R22|].
      split; [rewrite (KR 24%bv 24%nat eq_refl ltac:(cno_cs)); exact R24|].
      split; [rewrite (KR 25%bv 25%nat eq_refl ltac:(cno_cs)); exact R25|].
      split; [subst E2; change 48%nat with (32 + 16)%nat; rewrite ew_Ereg_extra; reflexivity|].
      split; [subst E2; change 49%nat with (32 + 17)%nat; rewrite ew_Ereg_extra; reflexivity|].
      split; [subst E2; change 50%nat with (32 + 18)%nat; rewrite ew_Ereg_extra; reflexivity|].
      cbn [ms_mem mkst].
      split.
      { apply (cno_zbytes_kept W3 W3 (ms_mem ms) mem' a (pn_copy (c_db cx) 65)); [|exact Hza1].
        intros j Hj. rewrite (cno_pn_length (c_db cx) 65) in Hj.
        apply (HBK a (cno_n cx + 18) j HaIn HaIn ltac:(rewrite Hreq; unfold cno_n in *; lia)).
        unfold cno_n in *. lia. }
      split.
      { apply (cno_zbytes_kept W3 W3 (ms_mem ms) mem' b (pn_copy (c_db cx) 66)); [|exact Hzb1].
        intros j Hj. rewrite (cno_pn_length (c_db cx) 66) in Hj.
        apply (HBK b (cno_n cx + 18) j HbIn HbIn ltac:(rewrite Hreq; unfold cno_n in *; lia)).
        unfold cno_n in *. lia. }
      split; [exact Pzt|].
      split.
      { apply (cno_rad_kept W3 W3 (ms_mem ms) mem' t (cno_n cx + 18) Hrad1).
        intros x Hx. apply Pkeep.
        - unfold SHADOW_OFF. Z.div_mod_to_equations. lia.
        - intros HQ.
          apply (fsw_ablock_off_shadow B ly3 S3 W3 (unpoison (c_U cx) (ms_mem ms)) _ t (cno_n cx + 18)
            (ARU_AR tfibsegs B ly3 S3 (c_U cx) W3 (ms_mem ms) _ HARU) HtIn (SHADOW_OFF + x / 8)
            ltac:(rewrite Hreq; lia)).
          unfold SHADOW_OFF. Z.div_mod_to_equations. lia.
        - intros HQ. unfold ESTACK in HQ. unfold SHADOW_OFF in HQ. Z.div_mod_to_equations. lia. }
      apply (cno_glob_ledger W3 W3 (ms_mem ms) mem' _ _ _ _); [|exact Hg1].
      intros y Hy. apply Pkeep.
      -- pose proof (fs_segs_low y (cno_pstat_img y Hy)). unfold kLowMemEnd in *. lia.
      -- intros HQ.
        exact (cno_blk_offfp ly3 S3 W3 (unpoison (c_U cx) (ms_mem ms)) _ t (cno_n cx + 18) y
          (ARU_AR tfibsegs B ly3 S3 (c_U cx) W3 (ms_mem ms) _ HARU)
          HtIn ltac:(rewrite Hreq; lia) Hy).
      -- intros HQ. pose proof (cno_pstat_bounds y Hy). unfold ESTACK in HQ. lia.
    * exact HSC2.
Qed.

(* ---- the span of lib/B/FSW_check_no_overread_inv.v ---- *)
Lemma cno_segM : segM_T B.
Proof. intros HD1. exact (cno_seg_M1 (cno_seg_M2 (cno_seg_M3 HD1))). Qed.
End M.

Check @cno_segM.
Print Assumptions cno_segM.
