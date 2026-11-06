(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/A/ACjr.v (equal, after the mapping, to the generic part of lib/YC4c.v) for libreac/fuzz_disco's program walk, over fuzz_disco's listing; mres_range states fuzz_disco.asan's image range as YImgTop's IMG_LO and IMG_TOP in place of cgif's literals; cgif's PC_INIT, lzw_MR, lzw_tabs and the kept_ctx/kept_ctx_m tactics of cgif's 72-byte LZW context block are left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoACjr.v, with its module paths changed; 136 of its 271 lines of code are new or changed and 109 lines of the source are left out. *)
(* fuzz_preset, program part: the after-call step kit of the program walks, the ONE copy (WalkS7b of h-rw-pre-5;
   every walk lane imports it). A PORT, not a re-authoring: the generic part of cgif's lib/A/AC8j.v
   (origin/ossv/recipes, proofs/cgif/cgif_file_fuzzer/lib/A/AC8j.v) restated over preset's journal YCbqG.v ajournal_x
   (allocator relation ARx a parameter with its laws AR_laws_x, ghost head sets Hp / Hpc, program statics PST) and the
   call-kept form YGcallx.v acall_kept_x. Generic: in segs (any image), B, PST, ARx; no image class, no address, no
   image numeral.
   What is ported (AC8j line -> here):
     st_ok_region_nth :43, slot_of_region :49, field_of_region :58, awr_ok_cons_gen :71, aview_kept_frame :80,
     blocks_bytes_after_malloc :87, region_kept_block_ajw :120 -> region_kept_block_ajx (ARx's alx_blocks gives the
     block's presence), writable_kept :133, region_kept_aview :142, val_mem_zero8 :153; the tactics getB / getLAWS /
     getTL :163-165 (over AR_laws_x / PALib), reseat :170 (over ajournal_x and YC1fP.v's jafter_call_keep_pi),
     kept_intrin :247, reshok_bx / reshok :249-256 -> reshok_sv (the shadow base an sv argument: preset's walks state
     their own Bx), norm_ss :257, eatom :258, rregU :259.
   Added, as the port needs them over ajournal_x (cgif has them over ajournal in lib/YCbq.v, here not in the preset
   core): img_env_havoc_hi (cgif's YC1f-family lemma of that name: a havoc at or above the image atoms keeps img_env),
   region_kept_stack_ajx (cgif YCbq.v:2601 region_kept_stack_aj over ajournal_x) and kept_stack (AC8j :219
   kept_malloc over it), region_kept_block_x (cgif YCbq.v:2624 region_kept_block_aj over acall_kept_x),
   acall_kept_x_mono_E (cgif YCbq.v:2708 over acall_kept_x).
   Not ported (cgif-specific): PC_INIT / lzw_* (:39-42, cgif's image), mres_kept / mres_range (:94-119, cgif's malloc
   post form), kept_ctx / kept_ctx_m (:222-246, cgif's context block numerals), getML / getAM / getAF / getENV
   (:166-169, cgif's runtime contract names).
   Numerals: 8 (LENGTH: a word), 33 (reseat's preserved env prefix, as AC8j :190: the entry registers and the stack
   atom), 2 (the stack atom's index, as AC8j :221 / :248). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YGcallx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YO0f.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section s.
Variable segs : list Segment.

(* AC8j :43 *)
Lemma st_ok_region_nth : forall E ss ms i r,
st_ok segs E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok segs E (ms_mem ms) r.
Proof.
intros E ss ms i r HS Hi. destruct (st_ok_mem_ok segs E ss ms HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.

(* AC8j :49 *)
Lemma slot_of_region : forall E m spe cs lo hi wlo whi od e v,
region_ok segs E m (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) ->
bv_unsigned (ew E 2) = spe -> In (YP09.mkChunk od (CVal 8 e)) cs -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
val_mem segs m (spe + od) 8 v.
Proof.
intros E m spe cs lo hi wlo whi od e v (_ & _ & _ & Hcs) H2 Hc He Hv.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite H2 in Hck.
change 8%nat with (N.to_nat 8). exact (val_of_chunk_ok segs E m spe od 8%N e v Hck He ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.

(* AC8j :58 *)
Lemma field_of_region : forall E m n b cs lo hi wlo whi od (w : N) e v,
region_ok segs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> sv_denot E e = Z_to_bv 64 v ->
0 <= v < 2 ^ (8 * Z.of_N w) -> (Z.of_N w <= 8) ->
val_mem segs m (b + od) (N.to_nat w) v.
Proof.
intros E m n b cs lo hi wlo whi od w e v (_ & _ & _ & Hcs) Hn Hc He Hv Hw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
exact (val_of_chunk_ok segs E m b od w e v Hck He Hv Hw).
Qed.

(* AC8j :71 (awr_ok / awr_byte are the engine's, YCbq.v:460 / :2152, as YC80x.v's runner takes them) *)
Lemma awr_ok_cons_gen : forall E r rs STK sp0 FP bl0 blc ly own n b,
YP09.r_base r = Some n -> bv_unsigned (ew E n) = b ->
(forall a, b + YP09.r_wlo r <= a < b + YP09.r_whi r -> awr_byte STK sp0 FP bl0 blc ly own a) ->
awr_ok E rs STK sp0 FP bl0 blc ly own -> awr_ok E (r :: rs) STK sp0 FP bl0 blc ly own.
Proof.
intros E r rs STK sp0 FP bl0 blc ly own n b Hb Hn Hw H a (r' & [<-|Hin] & Ha).
- rewrite Hb in Ha. cbn [base_val] in Ha. rewrite Hn in Ha. apply Hw. exact Ha.
- apply H. exists r'. auto.
Qed.

(* AC8j :80 *)
Lemma aview_kept_frame : forall E rs H (m m' : word -> option byte) lo,
frame_of E rs (mrestrict H m) (mrestrict H m') -> 0 <= lo ->
(forall a, lo <= a < 2 ^ 64 -> ~ in_wrange E rs a) ->
forall a, lo <= a < 2 ^ 64 -> aview segs H m' a = aview segs H m a.
Proof.
intros E rs H m m' lo HF Hlo Hno a Ha. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia. apply Hno. exact Ha.
Qed.

(* AC8j :133 *)
Lemma writable_kept : forall H (m m2 : word -> option byte) a,
(apresent H m a -> apresent H m2 a) -> writable_at segs (mrestrict H m) a -> writable_at segs (mrestrict H m2) a.
Proof.
intros H m m2 a Hp Hw. unfold writable_at, wview, mrestrict in *. revert Hw.
destruct (H (Z_to_bv 64 a)) eqn:EH; intros Hw; [exact Hw|].
destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em.
- destruct (Hp (conj EH (ex_intro _ b Em))) as [_ [b2 Hb2]]. rewrite Hb2. discriminate.
- destruct (m2 (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.

(* AC8j :142 *)
Lemma region_kept_aview : forall E H (m m2 : word -> option byte) n b lo hi wlo whi cs,
bv_unsigned (ew E n) = b ->
(forall a, b + lo <= a < b + hi -> aview segs H m2 a = aview segs H m a) ->
(forall a, apresent H m a -> apresent H m2 a) ->
region_kept segs E (mrestrict H m) (mrestrict H m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H m m2 n b lo hi wlo whi cs Hn Hav Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview segs). apply Hav. exact Ha.
- apply writable_kept. apply Hp.
Qed.

(* AC8j :153 *)
Lemma val_mem_zero8 : forall H (m : word -> option byte) a,
(forall i, 0 <= i < 8 -> aview segs H m (a + i) = Some 0) -> val_mem segs (mrestrict H m) a 8 0.
Proof.
intros H m a Hz j Hj. destruct (aview_byte segs H m (a + Z.of_nat j) 0 (Hz (Z.of_nat j) ltac:(lia))) as (b & Hb & Hv & _).
rewrite Hb. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap.
repeat (rewrite Z.shiftr_0_l || rewrite Z.mod_0_l by ((first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate]))). lia.
Qed.

(* cgif's img_env_havoc_hi: a havoc at or above the image atoms keeps img_env *)
Lemma img_env_havoc_hi : forall (val : nat -> Z) (lim : nat) E k ws,
img_env val lim E -> (lim <= k)%nat -> img_env val lim (havoc E k ws).
Proof. intros val lim E k ws HE Hk a Ha. rewrite ew_havoc_old by lia. exact (HE a Ha). Qed.

Section b.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx HL.
Local Notation AJ := (@ajournal_x rc SK segs B PST ARx).

(* AC8j :87 *)
Lemma blocks_bytes_after_malloc : forall ly1 S1 ly2 S2 (res n : Z) (P Q : Prop),
(res = 0 /\ ablocks B ly2 S2 = ablocks B ly1 S1 /\ P) \/ (4096 <= res /\ ablocks B ly2 S2 = ablocks B ly1 S1 ++ [(res, n)] /\ Q) ->
0 <= n -> blocks_bytes S2 <= blocks_bytes S1 + n.
Proof.
intros ly1 S1 ly2 S2 res n P Q Hres Hn. rewrite (blocks_bytes_bsum B ly2 S2), (blocks_bytes_bsum B ly1 S1).
destruct Hres as [(_ & -> & _) | (_ & -> & _)]; [lia|]. rewrite bsum_app. cbn. lia.
Qed.

(* cgif YCbq.v:2708 over acall_kept_x *)
Lemma acall_kept_x_mono_E : forall lyc Sc W memc W2 mem2 slo shi (E E' : Z -> Prop),
acall_kept_x segs B lyc Sc W memc W2 mem2 slo shi E -> (forall a, E a -> E' a) ->
acall_kept_x segs B lyc Sc W memc W2 mem2 slo shi E'.
Proof. intros. unfold acall_kept_x in *. eapply acall_kept_mono_E; eassumption. Qed.

(* cgif YCbq.v:2624 region_kept_block_aj over acall_kept_x: a read-only region in a live block the call keeps *)
Lemma region_kept_block_x : forall E lyc Sc W memc W2 mem2 slo shi (Er : Z -> Prop) n lo hi wlo whi cs b m,
acall_kept_x segs B lyc Sc W memc W2 mem2 slo shi Er ->
bv_unsigned (ew E n) = b -> In (b, m) (ablocks B lyc Sc) ->
0 <= lo -> hi <= req_size m -> whi <= wlo ->
(forall a, b + lo <= a < b + hi -> ~ Er a) ->
region_kept segs E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E lyc Sc W memc W2 mem2 slo shi Er n lo hi wlo whi cs b m HK. unfold acall_kept_x in HK.
exact (region_kept_block_aj segs B E lyc Sc W memc W2 mem2 slo shi Er n lo hi wlo whi cs b m HK).
Qed.

(* AC8j :120 region_kept_block_ajw over ARx: a writable region in a live block the call keeps; the block's presence
   after the call from ARx's alx_blocks *)
Lemma region_kept_block_ajx : forall E lyc Sc W memc W2 mem2 slo shi (Er : Z -> Prop) n lo hi cs b m ly2 S2 Hp2 md2,
acall_kept_x segs B lyc Sc W memc W2 mem2 slo shi Er -> ARx ly2 S2 Hp2 W2 mem2 md2 -> In (b, m) (ablocks B ly2 S2) ->
bv_unsigned (ew E n) = b -> In (b, m) (ablocks B lyc Sc) -> 0 <= lo -> hi <= req_size m ->
(forall a, b + lo <= a < b + hi -> ~ Er a) ->
region_kept segs E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some n) lo hi lo hi cs).
Proof.
intros E lyc Sc W memc W2 mem2 slo shi Er n lo hi cs b m ly2 S2 Hp2 md2 (_ & K2 & _) HAR2 Hin2 Hn Hin Hlo Hhi HnE.
destruct (alx_blocks segs B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 b m HAR2 Hin2) as (_ & _ & _ & _ & Hpres2 & _).
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview segs). replace a with (b + (a - b)) by lia. apply (K2 b m (a - b) Hin); [lia|].
replace (b + (a - b)) with a by lia. apply HnE. exact Ha.
- intros _. apply (apresent_writable segs). apply (proj1 (Hpres2 a ltac:(lia))).
Qed.

(* cgif YCbq.v:2601 region_kept_stack_aj over ajournal_x: a region of the caller's window, above the call's stack
   range, that a kept call leaves unchanged and present *)
Lemma region_kept_stack_ajx : forall E lyc Sc W memc W2 mem2 slo shi (Er : Z -> Prop) n lo hi wlo whi cs sp0 sp
STK FP ly S Hp W0 mem md own ly2 S2 Hp2 md2 k,
acall_kept_x segs B lyc Sc W memc W2 mem2 slo shi Er ->
AJ STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 k ->
bv_unsigned (ew E n) = sp -> shi <= sp + lo -> sp0 - STK <= sp + lo -> sp + hi <= sp0 -> lo <= wlo -> whi <= hi ->
region_kept segs E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E lyc Sc W memc W2 mem2 slo shi Er n lo hi wlo whi cs sp0 sp STK FP ly S Hp W0 mem md own ly2 S2 Hp2 md2 k
(K1 & _) HJ Hn Hshi Hlo Hhi Hw1 Hw2.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hal & Hstk0 & Hceil & Hslo & Hsh & H47 & _) & _).
pose proof asan_consts as (C1 & _).
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview segs). apply K1; lia.
- intros _. apply (apresent_writable segs). apply Hpres. lia.
Qed.
End b.
End s.
End c.

(* the realigned stack pointer of a prologue `andi sp, sp, -32`: x & (2^64 - 32) = x - x mod 32 (asked by BTx for
   tx_string, check_no_overread and put_string; the proof is S7bPutString's, moved here as the one copy) *)
Lemma land_m32 : forall x, 0 <= x < 2 ^ 64 -> Z.land x (2 ^ 64 - 32) = x - x mod 32.
Proof.
intros x Hx.
replace (2 ^ 64 - 32) with (Z.land (Z.ones 64) (Z.lnot (Z.ones 5))) by reflexivity.
rewrite Z.land_assoc, Z.land_ones, Z.mod_small by lia.
assert (Hl : Z.land x (Z.lnot (Z.ones 5)) = Z.ldiff x (Z.ones 5)).
{ apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.lnot_spec, Z.ldiff_spec by lia. reflexivity. }
rewrite Hl, Z.ldiff_ones_r, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2 ^ 5) with 32.
rewrite Z.mod_eq by lia. lia.
Qed.

(* ---- a listing slot's pc is below the run's allocation ceiling (the ONE copy; generic in L / PL / PI) ----
   The discharge of the fpre's `raZ regs < YM05.alloc_ceiling` at a call site whose return pc BASE + k is a slot of the
   listing: the slot's word is fetched from an image segment (pa_cert, pa_tbl_ok), so the pc is in_img, so below
   kLowMemEnd (pa_segs_low), which is below CEIL_MIN <= YM05.alloc_ceiling (YM05.alloc_ceiling_value). Same steps as
   YC1fP.v pa_slot_img, with pa_segs_low in place of pa_img_range. *)
Section pc. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {L : ptable asym} {PL : PAListing L} {PI : PAImg L}.
Lemma pa_slot_lt_ceil : forall k e, 0 <= k < 2 ^ 40 -> plookup pl_tpi k = Some e ->
  pa_val A_TEXT + k < YM05.alloc_ceiling.
Proof.
intros k e Hk40 Hk. pose proof pa_B_ok as HB. rewrite <- pl_tpi_eq in Hk.
pose proof (cert_slot asym (clookup pa_tbl) pa_val pa_sigma L pa_cert k e Hk) as [Hc Hk0].
unfold pi_slot_check in Hc.
destruct (clookup pa_tbl (pa_val A_TEXT + k)) as [wz|] eqn:Hf; [|discriminate].
pose proof (pa_tbl_ok _ _ Hf) as Hfw.
unfold fetch_word in Hfw. destruct (negb _); [discriminate|].
unfold code_read in Hfw.
destruct (find_segment pa_segs (bv_unsigned (Z_to_bv 64 (pa_val A_TEXT + k))) (Z.of_N 4)) as [sg|] eqn:Hfs; [|discriminate].
destruct (find_segment_hit _ _ _ _ Hfs) as (Hin & Hlo & Hhi).
assert (Himg : in_img pa_segs (bv_unsigned (Z_to_bv 64 (pa_val A_TEXT + k)))).
{ exists sg. split; [exact Hin|]. change (Z.of_N 4) with 4 in Hhi. lia. }
pose proof (pa_segs_low _ Himg) as HR.
rewrite Z_to_bv_unsigned in HR. unfold bv_wrap in HR. change (bv_modulus 64) with (2 ^ 64) in HR.
rewrite Z.mod_small in HR by lia.
pose proof (@YM05.alloc_ceiling_value rc) as [[HC _] _]. unfold kLowMemEnd in HR. lia.
Qed.
(* the same with an evar-free, boolean slot premise: discharge it by `vm_compute; reflexivity` on a CLOSED goal
   (S7bPjWrite measured: `eapply pa_slot_lt_ceil; [lia | vm_compute; reflexivity]` leaves `e` an evar under vm_compute and
   timed out at 120 s / 6.2 GB in a large context) *)
Lemma pa_slot_lt_ceil_b : forall k, 0 <= k < 2 ^ 40 ->
  match plookup pl_tpi k with Some _ => true | None => false end = true ->
  pa_val A_TEXT + k < YM05.alloc_ceiling.
Proof.
intros k Hk H. destruct (plookup pl_tpi k) as [e|] eqn:He; [|discriminate H].
exact (pa_slot_lt_ceil k e Hk He).
Qed.
End pc.

(* ---- the tactics (AC8j :163-273) ---- *)
Ltac getB := lazymatch goal with L : AR_laws_x _ ?Bv _ _ |- _ => Bv end.
Ltac getLAWS := lazymatch goal with L : AR_laws_x _ _ _ _ |- _ => L end.
Ltac getTL := lazymatch goal with T : PALib _ |- _ => T end.

(* AC8j :170: re-seat the symbolic state after a call. HS the state at the call, HJ2 the caller's journal after it (its
   world W2 and memory mem2), HP2 the callee's aregs_preserved, keep the indices of the regions to keep, AG the
   env-prefix fact `forall n, (n < 33)%nat -> ew E n = ew E0 n`, kept_tac the tactic that proves each kept region *)
Ltac reseat HS HJ2 HP2 keep AG kept_tac :=
let K := lazymatch type of HS with st_ok_pi _ _ _ ?ss _ => eval vm_compute in (run_K A_LIM (SOff 32 0) [] ss) | st_ok _ _ ?ss _ => eval vm_compute in (run_K A_LIM (SOff 32 0) [] ss) end in
let HS2 := fresh "HS2" in
lazymatch type of HJ2 with ajournal_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?W2 ?mem2 _ _ =>
lazymatch type of HP2 with aregs_preserved _ ?regs2 =>
jafter_call_keep_pi HS K regs2 (mrestrict (w_H W2) mem2) HP2 keep HS2 end end;
match type of HS2 with ?Q -> _ =>
let HQ := fresh "HQ" in
assert (HQ : Q); [ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil; kept_tac | specialize (HS2 HQ); clear HQ ] end;
clear HS; rewrite <- restrict_mkst_fx in HS2; rename HS2 into HS;
let AG2 := fresh "AG" in let Ev := fresh "E" in let HEv := fresh "HE" in
lazymatch type of AG with forall n, _ -> _ = ew ?E0 n =>
lazymatch type of HS with st_ok_pi _ _ ?Enew _ _ =>
remember Enew as Ev eqn:HEv in HS;
let HEIv := fresh "HEI" in
lazymatch type of HEv with
| _ = havoc ?Eo ?kk ?ws => lazymatch goal with Ho : img_env ?val ?lim Eo |- _ =>
pose proof (img_env_havoc_hi val lim Eo kk ws Ho ltac:(cbv; lia)) as HEIv; rewrite <- HEv in HEIv end
| _ = ?En => try (lazymatch goal with Hn : img_env _ _ En |- _ => rewrite <- HEv in Hn end) end;
repeat match goal with H : img_env _ _ (ewset _ _ _) |- _ => clear H end;
assert (AG2 : forall n, (n < 33)%nat -> ew Ev n = ew E0 n)
by (intros nn Hnn; rewrite HEv; rewrite ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; apply AG; exact Hnn);
repeat match goal with H : ew ?Eo ?n = ?v |- _ =>
lazymatch Eo with
| Ev => fail
| _ => lazymatch (eval cbv in (Nat.leb 33 n)) with
| true => let H2 := fresh H in
assert (H2 : ew Ev n = v) by (rewrite HEv; rewrite ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; exact H);
clear H; rename H2 into H
end end end;
clear HEv AG; rename AG2 into AG | st_ok _ ?Enew _ _ =>
remember Enew as Ev eqn:HEv in HS;
let HEIv := fresh "HEI" in
lazymatch type of HEv with
| _ = havoc ?Eo ?kk ?ws => lazymatch goal with Ho : img_env ?val ?lim Eo |- _ =>
pose proof (img_env_havoc_hi val lim Eo kk ws Ho ltac:(cbv; lia)) as HEIv; rewrite <- HEv in HEIv end
| _ = ?En => try (lazymatch goal with Hn : img_env _ _ En |- _ => rewrite <- HEv in Hn end) end;
repeat match goal with H : img_env _ _ (ewset _ _ _) |- _ => clear H end;
assert (AG2 : forall n, (n < 33)%nat -> ew Ev n = ew E0 n)
by (intros nn Hnn; rewrite HEv; rewrite ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; apply AG; exact Hnn);
repeat match goal with H : ew ?Eo ?n = ?v |- _ =>
lazymatch Eo with
| Ev => fail
| _ => lazymatch (eval cbv in (Nat.leb 33 n)) with
| true => let H2 := fresh H in
assert (H2 : ew Ev n = v) by (rewrite HEv; rewrite ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; exact H);
clear H; rename H2 into H
end end end;
clear HEv AG; rename AG2 into AG end end.

(* AC8j :219 kept_malloc, over region_kept_stack_ajx: a stack region of the caller kept by a call whose post gives
   acall_kept_x HK, inside the caller's journal HJ2; Usp the stack atom's value *)
Ltac kept_stack HK HJ2 AG Usp :=
eapply (region_kept_stack_ajx _ _ _ _ _);
[exact HK | exact HJ2 | cbn [ew ewset Nat.eqb]; rewrite ?(AG 2%nat) by lia; exact Usp | lia | lia | lia | cbn; lia | cbn; lia].

(* AC8j :247 *)
Ltac kept_intrin Hfr Hpres2 AG Usp :=
eapply region_kept_aview; [cbn [ew ewset Nat.eqb]; rewrite ?(AG 2%nat) by lia; exact Usp | intros a Ha; apply Hfr; unfold ESTACK; lia | exact Hpres2].

(* AC8j :249-256 reshok_bx / reshok are NOT ported: their shok_auto lived in Reusable/YC81.v, which the kit removed at
   2d523216ac5 (the cgif GIF-encoder listing island), and no walk used the port (reshok_sv, removed here). A walk
   re-seats its shadow tokens with its own sh_ok lemma. *)

(* AC8j :257-273 *)
Ltac norm_ss HS := lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS | st_ok _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
Ltac eatom AG Efact := cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?AG by lia; exact Efact.
Ltac rregU HS r v Utac H :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?Ex ?ss (restrict ?Hh ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
let rg := eval cbn [ms_regs restrict mkst] in (ms_regs ms) in
assert (H : getr rg r = Z_to_bv 64 v)
by (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ss ms r HS) _);
change (sv_denot Ex e = Z_to_bv 64 v); rewrite denot_lit_U; f_equal; Utac)
| st_ok ?segs ?Ex ?ss (restrict ?Hh ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
let rg := eval cbn [ms_regs restrict mkst] in (ms_regs ms) in
assert (H : getr rg r = Z_to_bv 64 v)
by (refine (eq_trans (st_ok_restrict_reg segs Hh Ex ss ms r HS) _);
change (sv_denot Ex e = Z_to_bv 64 v); rewrite denot_lit_U; f_equal; Utac)
end.
