(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: rec_shape_of's loop on fuzz_command.asan (0x89254 .. 0x892ec), in the form of
   proofs/cgif/cgif_file_fuzzer/lib/A/ACh2.v and ACh1.v (segment steps from one statement to the next, each seeded
   by the walk kit and run by the token-aware executor): the loop head with the inline check of the row and the
   strlen wrapper's call (HEAD -> R1), the length compare and the bcmp wrapper's call (R1 -> R2 / latch), the
   result test, the found branch's inline check and the return of the row's reply, and the latch to the next row
   or the return of "resp 0" after the last (R2 -> HEAD / return). One lemma per segment, for each of the 28
   rows. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/rec_shape_of_s.v, with its module paths and module names changed; 1230 of its 1273 lines of code are new or changed and 409 lines of the source are left out. *)
(* check_words_add's walk on the ASan+UBSan build of plugin-hostd/fuzz_command, part 4: the head 0x88eac .. 0x88f64
   (listing offsets 0x297c .. 0x2a34). The B twin of lib/A/Prog/check_words_add_s4.v (a working branch
   1aea12cabb8).

   The prologue (frame 64, ra and s0..s5 saved), the shadow base read through the GOT word 0xa5f50 and the
   cell 0xb0c38, the branch on `read < 4`, the trap sites of w + 24 (0x88ef4 w null, 0x88efc w past 2^64 - 24,
   0x88f08 (w + 24) & 7), which the run decides not taken from the fact on atom 11 (w: at or above 4072 by its
   slot's block, 8-aligned by the statement's `wp mod 8 = 0`), the inline check of w[3], and the three wrapper
   calls that decide whether the placement is w[3] ("own", "default", or a "pool:" prefix) or the image literal
   "-" 0x21b00. The five paths join at 0x88f64, where lib/B/Prog/check_words_add_s2.v's `cwa_mid_dash` (the
   literal) and lib/B/Prog/check_words_add_s3.v's `cwa_mid_word` (the word) take over.

   The facts about the image that the statement does not give are the record CwaFacts of
   lib/B/Prog/check_words_add_s1.v; this file adds nothing about B. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YI09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import CommandTac.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require check_words_add_c.
Module PCwa := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.check_words_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import check_words_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaRun PaShadow PaJournal CmdSyms CmdList CmdAddr CmdPa CmdPaLib CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaCall PaCallRun PaDenot PaArt PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
check_words_add_s1 check_words_add_s2 check_words_add_s3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Ltac cwh_unf := repeat first [ progress unfold CALL_OFF_NARGS in * | progress unfold CALL_OFF_ARGS in * ];
cwa_unf.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Section e.
Variable B : asyms.
Variables RLO RHI : Z.
Hypothesis HFACTS : CwaFacts B.

(* ---- what the walk carries across the frame stores and the wrapper calls -------------------------- *)

Lemma cwh_kept_wide : forall (rd rd' : reader) lo hi lo' hi',
kept_out rd rd' lo hi -> lo' <= lo -> hi <= hi' -> kept_out rd rd' lo' hi'.
Proof. intros rd rd' lo hi lo' hi' HK H1 H2 a Ha Hn. apply HK; [exact Ha | lia]. Qed.

(* the memory a run leaves alone: every byte outside the write windows of the state's regions *)
Lemma cwh_mem_kept : forall E (W : world SEGS) (m m' : word -> option byte) (rs : smem) lo hi,
frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
(forall b wlo whi a, In (b, wlo, whi) (windows rs) ->
 base_val E b + wlo <= a < base_val E b + whi -> lo <= a < hi) ->
kept_out (rdW W m) (rdW W m') lo hi.
Proof.
intros E W m m' rs lo hi HFR HW a Ha Hn.
exact (kept_of_frame (segs := SEGS) E rs (w_H W) m m' (fun x => lo <= x < hi) HFR HW a Ha Hn).
Qed.

Lemma cwh_val_kept : forall (W : world SEGS) m m' lo hi a n v,
kept_out (rdW W m) (rdW W m') lo hi -> aval_mem (rdW W m) a n v ->
0 <= a -> a + Z.of_nat n <= lo -> lo < 2 ^ 64 -> aval_mem (rdW W m') a n v.
Proof.
intros W m m' lo hi a n v HK H Ha Hn Hlo k Hk.
rewrite (HK (a + Z.of_nat k) ltac:(lia) ltac:(lia)). exact (H k Hk).
Qed.

(* the read-only bytes of the image: every address the list names lies below 0x606000 *)
Lemma cwh_ro_kept : forall (rd rd' : reader) lo hi,
kept_out rd rd' lo hi -> 0x700000 <= lo -> lo < 2 ^ 64 -> cmd_ro_ok rd -> cmd_ro_ok rd'.
Proof.
intros rd rd' lo hi HK Hlo Hhi [HB HT].
assert (HG : forall a l, abytes_atR rd a l -> 0 <= a -> a + Z.of_nat (length l) <= lo -> abytes_atR rd' a l)
by (intros a l H Ha Hl; exact (abytes_atR_kept rd rd' lo hi a l HK H Ha Hl Hhi)).
split.
- unfold cmd_ro_bytes in HB |- *.
  repeat match goal with H : _ /\ _ |- _ => destruct H as [? H] end.
  repeat split;
  lazymatch goal with
  | |- abytes_atR _ ?a ?l =>
    lazymatch goal with
    | Hx : abytes_atR rd a l |- _ =>
      apply (HG a l Hx);
      [lia | assert (HL : Z.of_nat (length l) <= 100000)
             by (apply (proj1 (Z.leb_le _ _)); vm_compute; reflexivity); lia]
    end
  end.
- intros e He a Ha.
  assert (HE : forallb (fun z => (0 <=? z) && (z <=? 0x606000)) cmd_ro_ends = true)
  by (vm_compute; reflexivity).
  rewrite forallb_forall in HE. specialize (HE e He).
  apply andb_true_iff in HE as [HE1 HE2]. apply Z.leb_le in HE1. apply Z.leb_le in HE2.
  pose proof (Z.mod_pos_bound e 8 ltac:(lia)) as Hm.
  rewrite (HK a ltac:(lia) ltac:(lia)). exact (HT e He a Ha).
Qed.

(* a string argument of the statement, at a memory that agrees with the entry's below the stack window *)
Lemma cwh_argA_kept : forall ly S W (rg : bvmap 5 word) mem md m' lo hi p x,
AR SEGS B ly S W mem md -> alloc_ceiling <= spZ rg - 2 * ESTACK ->
cwa_str B ly S (rdW W mem) p x ->
kept_out (rdW W mem) (rdW W m') lo hi -> alloc_ceiling <= lo -> lo < 2 ^ 64 ->
cwa_str B ly S (rdW W m') p x.
Proof.
intros ly S W rg mem md m' lo hi p x HAR Hsp HA HK Hlo Hhi.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (cwa_str_facts B ly S W rg mem md p x HAR HA Hsp)
as (Hp0 & _ & _ & _ & Hb & Hp64).
unfold astr_len in Hb.
destruct HA as (H0 & H1 & H2).
split; [exact H0|]. split; [exact H1|].
exact (astr_atR_kept _ _ lo hi p x HK H2 ltac:(lia) ltac:(lia) Hhi).
Qed.

(* one of the seven words the prologue saved, read back out of the walk's frame region *)
Lemma cwh_frame_field : forall (E' : env) (W : world SEGS) (m : word -> option byte) cs sp0 od (n : nat) (v : word),
region_ok SEGS E' (mrestrict (w_H W) m) (YP09.mkRegion (Some 2%nat) (-64) 0 (-64) 0 cs) ->
bv_unsigned (ew E' 2) = sp0 -> In (YP09.mkChunk od (CVal 8 (SOff n 0))) cs -> ew E' n = v ->
val_mem SEGS (mrestrict (w_H W) m) (sp0 + od) 8 (bv_unsigned v).
Proof.
intros E' W m cs sp0 od n v HR H2 Hin Hv.
pose proof (bv_unsigned_in_range 64 v) as HV. change (bv_modulus 64) with (2 ^ 64) in HV.
replace 8%nat with (N.to_nat 8) by reflexivity.
apply (field_of_region E' (mrestrict (w_H W) m) 2%nat sp0 cs (-64) 0 (-64) 0 od 8%N (SOff n 0)
(bv_unsigned v) HR H2 Hin).
- cbn [sv_denot]. rewrite Hv, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- cbn. lia.
- cbn. lia.
Qed.

(* all seven, in the form the mid and tail lemmas take them *)
Lemma cwh_frame_all : forall (E' : env) (W : world SEGS) (m : word -> option byte) sp0 (rg : bvmap 5 word),
region_ok SEGS E' (mrestrict (w_H W) m)
(YP09.mkRegion (Some 2%nat) (-64) 0 (-64) 0
 [YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0));
  YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
  YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
  YP09.mkChunk (-8) (CVal 8 (SOff 1 0))]) ->
bv_unsigned (ew E' 2) = sp0 ->
(forall (n : nat) (rr : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned rr -> ew E' n = getr rg rr) ->
cwa_frame (mrestrict (w_H W) m) sp0 rg.
Proof.
intros E' W m sp0 rg HR H2 HEN.
assert (HF : forall od (n : nat) (rr : bv 5),
 In (YP09.mkChunk od (CVal 8 (SOff n 0)))
 [YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0));
  YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
  YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
  YP09.mkChunk (-8) (CVal 8 (SOff 1 0))] ->
 (n < 32)%nat -> Z.of_nat n = bv_unsigned rr ->
 val_mem SEGS (mrestrict (w_H W) m) (sp0 + od) 8 (bv_unsigned (getr rg rr)))
by (intros od n rr Hin Hn Hrr;
    exact (cwh_frame_field E' W m _ sp0 od n (getr rg rr) HR H2 Hin (HEN n rr Hn Hrr))).
unfold cwa_frame.
split; [replace (sp0 - 8) with (sp0 + (-8)) by lia;
        exact (HF (-8) 1%nat 1%bv ltac:(cbn [In]; repeat first [left; reflexivity | right]) ltac:(lia) eq_refl)|].
split; [replace (sp0 - 16) with (sp0 + (-16)) by lia;
        exact (HF (-16) 8%nat 8%bv ltac:(cbn [In]; repeat first [left; reflexivity | right]) ltac:(lia) eq_refl)|].
split; [replace (sp0 - 24) with (sp0 + (-24)) by lia;
        exact (HF (-24) 9%nat 9%bv ltac:(cbn [In]; repeat first [left; reflexivity | right]) ltac:(lia) eq_refl)|].
split; [replace (sp0 - 32) with (sp0 + (-32)) by lia;
        exact (HF (-32) 18%nat 18%bv ltac:(cbn [In]; repeat first [left; reflexivity | right]) ltac:(lia) eq_refl)|].
split; [replace (sp0 - 40) with (sp0 + (-40)) by lia;
        exact (HF (-40) 19%nat 19%bv ltac:(cbn [In]; repeat first [left; reflexivity | right]) ltac:(lia) eq_refl)|].
split; [replace (sp0 - 48) with (sp0 + (-48)) by lia;
        exact (HF (-48) 20%nat 20%bv ltac:(cbn [In]; repeat first [left; reflexivity | right]) ltac:(lia) eq_refl)|].
replace (sp0 - 56) with (sp0 + (-56)) by lia.
exact (HF (-56) 21%nat 21%bv ltac:(cbn [In]; repeat first [left; reflexivity | right]) ltac:(lia) eq_refl).
Qed.

Lemma cwh_dash_eqb : bytes_eqb S_DASH S_DASH = true.
Proof. vm_compute. reflexivity. Qed.

(* the client the recorded call names when the placement is the literal "-" *)
Lemma cwh_client_dash : forall r (w3 w4 : list byte), (3 <? r) && PCwa.is_placement_b w3 = false ->
PCwa.add_client r w3 w4 = (if 3 <? r then w3 else S_DASH).
Proof.
intros r w3 w4 H. unfold PCwa.add_client, PCwa.add_next, PCwa.add_placement.
rewrite H, cwh_dash_eqb. destruct (3 <? r); reflexivity.
Qed.

(* an image literal the wrapper calls read, in the form their contracts take it *)
Lemma cwh_lit_str : forall ly S W (rg : bvmap 5 word) mem md a n (l s : list byte),
AR SEGS B ly S W mem md -> cmd_ro_ok (rdW W mem) -> alloc_ceiling <= spZ rg - 2 * ESTACK ->
In (a, n) CWA_LITS -> abytes_atR (rdW W mem) a l -> In (a + n - 1) cmd_ro_ends ->
l = s ++ [Z_to_bv 8 0] -> ~ In (Z_to_bv 8 0) s -> Z.of_nat (length l) = n ->
astr_at SEGS W mem a s /\ aread_ok SEGS (2 * ESTACK) W rg mem a (astr_len s + 1)
/\ atail_vis SEGS W mem (a + astr_len s).
Proof.
intros ly S W rg mem md a n l s HAR HRO Hsp Hin Hb Hend Hls Hns Hlen.
destruct (cwa_lit_facts B HFACTS ly S W rg mem md a n l HAR Hin Hb Hlen HRO Hend Hsp)
as [HRD HTL].
assert (HLS : astr_len s + 1 = n)
by (unfold astr_len; rewrite Hls, length_app in Hlen; cbn [length] in Hlen; lia).
split; [|split].
- split; [|exact Hns]. apply abytes_atR_view. rewrite <- Hls. exact Hb.
- rewrite HLS. exact HRD.
- replace (a + astr_len s) with (a + n - 1) by lia. exact HTL.
Qed.

(* a region with a write window survives a wrapper call: its bytes are outside the call's scratch
   window, and the journal keeps every byte of the walk's own frame present *)
Lemma cwh_region_kept_w : forall E (W : world SEGS) memc mem2 (r : YP09.region) lo hi,
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> rdW W mem2 a = rdW W memc a) ->
0 <= base_val E (YP09.r_base r) + YP09.r_lo r -> base_val E (YP09.r_base r) + YP09.r_hi r <= 2 ^ 64 ->
(base_val E (YP09.r_base r) + YP09.r_hi r <= lo \/ hi <= base_val E (YP09.r_base r) + YP09.r_lo r) ->
(forall a, base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r ->
 apresent (w_H W) mem2 a) ->
region_kept SEGS E (mrestrict (w_H W) memc) (mrestrict (w_H W) mem2) r.
Proof.
intros E W memc mem2 r lo hi HK H0 H1 Hap Hpr. split; intros a Ha.
- apply (mbyte_of_aview SEGS). apply HK; lia.
- intros _. apply apresent_writable. exact (Hpr a Ha).
Qed.

(* a shorter prefix of a readable range is readable: what the strncmp wrapper asks for *)
Lemma cwh_read_shrink : forall stk (W : world SEGS) (rg : bvmap 5 word) mem x n n',
aread_ok SEGS stk W rg mem x n -> 0 <= n' <= n -> aread_ok SEGS stk W rg mem x n'.
Proof.
intros stk W rg mem x n n' (H0 & H1 & H2 & H3 & H4 & H5 & H6) Hn.
split; [exact H0|]. split; [lia|]. split; [lia|].
split; [intros a Ha; apply H3; lia|].
split; [unfold amem_range in *; lia|].
split; [eapply range_addressable_sub; [exact H5 | lia | lia]|].
intros Hpos. pose proof (H6 ltac:(lia)) as Hh. intros s Hs. apply Hh.
assert (HM : shadow_addr (x + n' - 1) <= shadow_addr (x + n - 1))
by (unfold shadow_addr; pose proof (Z.div_le_mono (x + n' - 1) (x + n - 1) 8 ltac:(lia) ltac:(lia)); lia).
assert (HD : shadow_addr (x + n' - 1) / 8 <= shadow_addr (x + n - 1) / 8)
by (apply Z.div_le_mono; lia).
lia.
Qed.

Lemma cwh_zero_iff : forall (v : word), v = w64 0 <-> bv_unsigned v = 0.
Proof.
intros v. split; [intros ->; reflexivity | intros H; apply bv_eq; rewrite H; reflexivity].
Qed.

Lemma cwh_not_dash : forall w, PCwa.is_placement_b w = true -> bytes_eqb w S_DASH = false.
Proof.
intros w H. destruct (bytes_eqb w S_DASH) eqn:Eq; [|reflexivity].
apply bytes_eqb_iff in Eq. subst w. vm_compute in H. discriminate.
Qed.

(* the placement and the client the recorded call names when word 3 is a placement word *)
Lemma cwh_client_word : forall r (w3 w4 : list byte), 3 < r -> PCwa.is_placement_b w3 = true ->
PCwa.add_placement r w3 = w3 /\ PCwa.add_client r w3 w4 = (if 4 <? r then w4 else S_DASH).
Proof.
intros r w3 w4 Hr Hp.
assert (Hlt : (3 <? r) = true) by (apply Z.ltb_lt; lia).
assert (HP : PCwa.add_placement r w3 = w3)
by (unfold PCwa.add_placement; rewrite Hlt, Hp; reflexivity).
split; [exact HP|].
unfold PCwa.add_client, PCwa.add_next. rewrite HP, (cwh_not_dash w3 Hp).
destruct (4 <? r); reflexivity.
Qed.

Let RUN := paj_run B (cwa_laws B).
Let RUNTO := paj_run_to B (cwa_laws B).
Let BR := paj_branch (PI := PI).

Lemma cwa_head : forall ly S W (regs : bvmap 5 word) mem md (cp wp r nargs p3 p4 q2 q3 : Z)
(w3 w4 x2 x3 : list byte),
astrcmp_realizes SEGS B (SIGMA CS___interceptor_trampoline_strcmp) ->
astrncmp_realizes SEGS B (SIGMA CS___interceptor_trampoline_strncmp) ->
afn_pre_na SEGS B CHECK_WORDS_ADD_STK ly S W regs mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
getr regs 10 = w64 cp -> getr regs 11 = w64 wp -> getr regs 12 = w64 r ->
0 <= r <= 64 ->
cmd_ro_ok (rdW W mem) ->
cmd_val_objs ->
A_G_REC + OFF_CALLS <= cp -> cp + CALL_SIZE <= A_G_REC + REC_SIZE -> cp mod 8 = 0 ->
aval_mem (rdW W mem) (cp + CALL_OFF_NARGS) 4 nargs -> 0 <= nargs <= 6 ->
(nargs = 4 ->
 aval_mem (rdW W mem) (cp + CALL_OFF_ARGS + 16) 8 q2 /\
 cwa_str B ly S (rdW W mem) q2 x2) ->
(nargs = 4 ->
 aval_mem (rdW W mem) (cp + CALL_OFF_ARGS + 24) 8 q3 /\
 cwa_str B ly S (rdW W mem) q3 x3) ->
(3 < r ->
 in_blockA (ablocks B ly S) (wp + 24) 8 /\ aval_mem (rdW W mem) (wp + 24) 8 p3 /\
 cwa_str B ly S (rdW W mem) p3 w3) ->
(4 < r ->
 in_blockA (ablocks B ly S) (wp + 32) 8 /\ aval_mem (rdW W mem) (wp + 32) 8 p4 /\
 cwa_str B ly S (rdW W mem) p4 w4) ->
wp mod 8 = 0 ->
nargs = 4 -> x2 = PCwa.add_placement r w3 -> x3 = PCwa.add_client r w3 w4 ->
st_nev S + EV_CHECK_WORDS_ADD <= EV_MAX ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0x297c)) mem (seg_rom SEGS)) md)
(apost_base SEGS B CHECK_WORDS_ADD_STK [] regs ly S W mem md 0
(fun ly' S' W' regs' mem' md' => Permutation (ablocks B ly' S') (ablocks B ly S) /\ ly' = ly /\ S' = S)).
Proof.
intros ly S W regs mem md cp wp r nargs p3 p4 q2 q3 w3 w4 x2 x3
ASTRCMP ASTRNCMP HPRE HRO R10 R11 R12 Hr HROK VOBJS Hcp1 Hcp2 Hcp8 HN Hnb HQ2 HQ3 AW3 AW4 Hwp8 HNA HX2 HX3 HEV.
rewrite HNA in HN, HQ2, HQ3.
destruct (HQ2 eq_refl) as [HV2 AQ2]. destruct (HQ3 eq_refl) as [HV3 AQ3].
clear HQ2 HQ3.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (WS : CHECK_WORDS_ADD_STK = 8256) by reflexivity.
assert (Hsp2 : alloc_ceiling <= spZ regs - 2 * ESTACK) by (cwa_unf; lia).
assert (HJ : ajournal SEGS B CHECK_WORDS_ADD_STK (spZ regs) [] ly S W mem md [] ly S W mem md 0)
by (eapply ajournal_init_na; exact HPRE).
destruct (cwa_entry B HFACTS ly S W regs mem md cp wp r 4 p3 p4 q2 q3 HPRE VOBJS R12 Hr)
as [HS SHOK].
set (E := cwa_E regs p3 p4 q2 q3 4) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, cwa_E; apply Eimg_env).
assert (EN : forall (n : nat) (rr : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned rr ->
ew E n = getr regs rr)
by (intros n rr Hn Hrr; unfold E, cwa_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hrr).
assert (EX : forall j, (j < 6)%nat -> ew E (32 + j) = nth j (cwa_extra p3 p4 q2 q3 4) (Z_to_bv 64 0))
by (intros j Hj; unfold E, cwa_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as Ea32. cbn [Nat.add nth cwa_extra map] in Ea32.
assert (Ea270 : ew E 270 = Z_to_bv 64 (VAL (A_OBJ 29)))
by (unfold E, cwa_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (VO29 : VAL (A_OBJ 29) = 0x21b00)
by (rewrite (VOBJS 29%nat ltac:(vm_compute; lia)); vm_compute; reflexivity).
pose proof (EX 1%nat ltac:(lia)) as Ea33. cbn [Nat.add nth cwa_extra map] in Ea33.
assert (Ea241 : ew E 241 = Z_to_bv 64 (VAL (A_OBJ 0)))
by (unfold E, cwa_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Ea253 : ew E 253 = Z_to_bv 64 (VAL (A_OBJ 12)))
by (unfold E, cwa_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (VO0 : VAL (A_OBJ 0) = 0xa5f50)
by (rewrite (VOBJS 0%nat ltac:(vm_compute; lia)); vm_compute; reflexivity).
assert (VO12 : VAL (A_OBJ 12) = 0xb0c38)
by (rewrite (VOBJS 12%nat ltac:(vm_compute; lia)); vm_compute; reflexivity).
assert (BG : bv_unsigned (ew E 241) = 0xa5f50)
by (rewrite Ea241, VO0; apply unsigned_lit_small; lia).
assert (BC : bv_unsigned (ew E 253) = 0xb0c38)
by (rewrite Ea253, VO12; apply unsigned_lit_small; lia).
assert (Esp : bv_unsigned (ew E 2) = spZ regs)
by (rewrite (EN 2%nat 2%bv ltac:(lia) eq_refl); reflexivity).
paj_run_tok RUN HS HJ SHOK CWA_SPAN; [awr_ok_tac; exact Esp |].
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdq) _ => set (mdv1 := mdq) in *; clearbody mdv1 end.
assert (K1 : kept_out (rdW W mem) (rdW W (ms_mem ms)) (spZ regs - 64) (spZ regs)).
{ apply (cwh_mem_kept E W mem (ms_mem ms) cwa_regions0); [exact HFr|].
  intros b wlo whi a Hin Hr'.
  cbv [cwa_regions0 stack_region got_regionP bcell_regionP windows] in Hin.
  cbn [map In YP09.r_base YP09.r_wlo YP09.r_whi] in Hin.
  destruct Hin as [Heq | [Heq | [Heq | []]]]; inversion Heq; subst;
  cbn [base_val] in Hr'; rewrite ?Esp in Hr'; lia. }
clear HF HFr HG.
assert (HRr : sv_denot E (SOff 12 0) = Z_to_bv 64 r)
by (cbn [sv_denot]; rewrite (EN 12%nat 12%bv ltac:(lia) eq_refl), R12, Z.add_0_r;
    unfold w64; apply Z_to_bv_bv_unsigned).
assert (HR4 : sv_denot E (SLit 4) = Z_to_bv 64 4) by reflexivity.
psrr_branch_tok RUN BR HS SHOK CWA_SPAN.
- (* read < 4: the placement stays the image literal "-" *)
  rewrite (cwa_branch_lt _ _ _ r 4 HRr HR4 ltac:(lia) ltac:(lia)) in Hc.
  apply Z.ltb_lt in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK CWA_SPAN 0x2a34; [awr_ok_tac; exact Esp |].
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdq) _ => set (mdv2 := mdq) in *; clearbody mdv2 end.
  assert (K2 : kept_out (rdW W (ms_mem ms)) (rdW W (ms_mem ms0)) (spZ regs - 64) (spZ regs)).
  { apply (cwh_mem_kept _ W _ _ _ _ _ HFr).
    intros b wlo whi a Hin Hr'.
    cbv [windows] in Hin. cbn [map In YP09.r_base YP09.r_wlo YP09.r_whi] in Hin.
    repeat (destruct Hin as [Heq | Hin];
            [inversion Heq; subst; cbn [base_val] in Hr'; rewrite ?Esp in Hr'; lia |]);
    destruct Hin. }
  assert (K12 : kept_out (rdW W mem) (rdW W (ms_mem ms0)) (spZ regs - 64) (spZ regs))
  by (exact (kept_out_trans _ _ _ _ _ _ _ K1 K2 ltac:(lia) ltac:(lia))).
  (* the frame the prologue wrote *)
  assert (HFRM : cwa_frame (mrestrict (w_H W) (ms_mem ms0)) (spZ regs) regs).
  { pose proof (st_ok_region_nth (segs := SEGS) _ _ _ 0%nat _ HS eq_refl) as HRG.
    cbn [ms_mem restrict] in HRG.
    exact (cwh_frame_all _ W _ (spZ regs) regs HRG Esp EN). }
  (* the bytes the mid lemma reads *)
  assert (ROKc : cmd_ro_ok (rdW W (ms_mem ms0)))
  by (exact (cwh_ro_kept _ _ _ _ K12 ltac:(cwa_unf; lia) ltac:(cwa_unf; lia) HROK)).
  assert (HNc : aval_mem (rdW W (ms_mem ms0)) (cp + CALL_OFF_NARGS) 4 4)
  by (exact (cwh_val_kept W mem (ms_mem ms0) _ _ _ 4%nat 4 K12 HN
      ltac:(cwh_unf; lia) ltac:(cwh_unf; lia) ltac:(cwa_unf; lia))).
  assert (HQ2c : aval_mem (rdW W (ms_mem ms0)) (cp + CALL_OFF_ARGS + 16) 8 q2)
  by (exact (cwh_val_kept W mem (ms_mem ms0) _ _ _ 8%nat q2 K12 HV2
      ltac:(cwh_unf; lia) ltac:(cwh_unf; lia) ltac:(cwa_unf; lia))).
  assert (HQ3c : aval_mem (rdW W (ms_mem ms0)) (cp + CALL_OFF_ARGS + 24) 8 q3)
  by (exact (cwh_val_kept W mem (ms_mem ms0) _ _ _ 8%nat q3 K12 HV3
      ltac:(cwh_unf; lia) ltac:(cwh_unf; lia) ltac:(cwa_unf; lia))).
  assert (Hlt3 : (3 <? r) = false) by (apply Z.ltb_ge; lia).
  assert (HX2D : x2 = S_DASH)
  by (rewrite HX2; unfold PCwa.add_placement; rewrite Hlt3; reflexivity).
  assert (AQ2c : cwa_str B ly S (rdW W (ms_mem ms0)) q2 S_DASH).
  { rewrite <- HX2D.
    exact (cwh_argA_kept ly S W regs mem md (ms_mem ms0) _ _ q2 x2 HAR0 Hsp2 AQ2 K12
    ltac:(cwa_unf; lia) ltac:(cwa_unf; lia)). }
  assert (AQ3c : cwa_str B ly S (rdW W (ms_mem ms0)) q3 x3)
  by (exact (cwh_argA_kept ly S W regs mem md (ms_mem ms0) _ _ q3 x3 HAR0 Hsp2 AQ3 K12
      ltac:(cwa_unf; lia) ltac:(cwa_unf; lia))).
  assert (HXD : x3 = (if 3 <? r then w3 else S_DASH))
  by (rewrite HX3; apply cwh_client_dash; rewrite Hlt3; reflexivity).
  (* the registers at 0x88f64 *)
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18.
  prreg HS (19%bv : bv 5) P19. prreg HS (21%bv : bv 5) P21.
  assert (T2 : getr (ms_regs ms0) 2 = w64 (spZ regs - 64))
  by (rewrite P2, Esp; unfold w64; f_equal; lia).
  assert (T3 : getr (ms_regs ms0) 3 = getr regs 3)
  by (rewrite P3; exact (EN 3%nat 3%bv ltac:(lia) eq_refl)).
  assert (T4 : getr (ms_regs ms0) 4 = getr regs 4)
  by (rewrite P4; exact (EN 4%nat 4%bv ltac:(lia) eq_refl)).
  assert (T8 : getr (ms_regs ms0) 8 = w64 cp)
  by (rewrite P8, (EN 10%nat 10%bv ltac:(lia) eq_refl); exact R10).
  assert (T9 : getr (ms_regs ms0) 9 = w64 0x21b00)
  by (rewrite P9, Ea270, VO29; reflexivity).
  assert (T18 : getr (ms_regs ms0) 18 = w64 wp)
  by (rewrite P18, (EN 11%nat 11%bv ltac:(lia) eq_refl); exact R11).
  assert (T19 : getr (ms_regs ms0) 19 = w64 r)
  by (rewrite P19, (EN 12%nat 12%bv ltac:(lia) eq_refl); exact R12).
  assert (T21 : getr (ms_regs ms0) 21 = w64 SHADOW_OFF)
  by (rewrite P21, Ea32; reflexivity).
  assert (Thi : forall rr, 22 <= rr <= 27 -> getr (ms_regs ms0) (Z_to_bv 5 rr) = getr regs (Z_to_bv 5 rr)).
  { intros rr Hrr.
    assert (Hc' : rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia.
    repeat (destruct Hc' as [-> | Hc']); [..|subst rr];
    lazymatch goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
      let G := fresh "G" in prreg HS (Z_to_bv 5 k) G; rewrite G end;
    lazymatch goal with |- ew _ ?n = getr _ ?r2 =>
      exact (EN n r2 ltac:(lia) eq_refl) end. }
  exact (cwa_mid_dash B RLO RHI HFACTS ly S W regs mem md cp q2 q3 wp r p3 x3 w3
  (ms_mem ms0) mdv2 (ms_regs ms0) HPRE HRO HJ VOBJS ASTRCMP ROKc T2 T3 T4 Thi T8 T9 T18 T19 T21
  Hr HFRM Hcp1 Hcp2 Hcp8 Hwp8 HNc HQ2c HQ3c AQ2c AQ3c ltac:(intros HC; exfalso; lia) HXD).
- (* read > 3: the inline check of w[3], then the three wrapper calls *)
  rewrite (cwa_branch_lt _ _ _ r 4 HRr HR4 ltac:(lia) ltac:(lia)) in Hc.
  apply Z.ltb_ge in Hc. rename Hc into Hr4.
  pose proof (proj1 HJ) as HARc.
  destruct (AW3 ltac:(lia)) as (HBK & HVW & AP3).
  destruct HBK as (qb & kb & Hinb & Hqb1 & Hqb2).
  destruct (al_blocks _ _ (cwa_laws B) _ _ _ _ _ qb kb HAR0 Hinb)
  as (Hb16 & Hb4096 & Hbceil & Hbia & Hbpres & _).
  pose proof (req_size_pos kb ltac:(lia)) as [Hk1 Hk2].
  pose proof (blk_off_imgP B ly S W mem md qb kb HAR0 Hinb) as HOFF.
  unfold off_img in HOFF.
  destruct (cwa_str_facts B ly S W regs mem md p3 w3 HAR0 AP3 Hsp2)
  as (Hp30 & SP3 & RP3 & TP3 & Bp3 & Rp3).
  assert (HVWc : aval_mem (rdW W (ms_mem ms)) (wp + 24) 8 p3)
  by (exact (cwh_val_kept W mem (ms_mem ms) _ _ _ 8%nat p3 K1 HVW
      ltac:(cwa_unf; lia) ltac:(cwa_unf; lia) ltac:(cwa_unf; lia))).
  assert (HRAW : range_addressable (rdW W (ms_mem ms)) SHADOW_OFF qb (req_size kb))
  by (exact (range_addressable_of_block SEGS B (cwa_laws B) ly S W (ms_mem ms) mdv1 qb kb qb
      (req_size kb) HARc Hinb ltac:(lia) ltac:(lia))).
  assert (BW : bv_unsigned (ew E 11) = wp)
  by (rewrite (EN 11%nat 11%bv ltac:(lia) eq_refl), R11; unfold w64;
      apply unsigned_lit_small; cwa_unf; lia).
  assert (Usb : bv_unsigned (ew E 32) = SHADOW_OFF)
  by (rewrite Ea32; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  (* the slot w + 24 as a region of the walk, with its atom's bounds and its shadow entry; atom 11 (w) at or
     above 4072 and 8-aligned (`wp mod 8 = 0`), so the run decides the trap branches 0x88ef4, 0x88efc and 0x88f08
     not taken *)
  apply (st_ok_pi_add_fact _ _ _ 11%nat (mkAF 4072 140737479966720 3)) in HS;
  [| unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite BW; change (2 ^ 3) with 8;
     cwa_unf; repeat split; lia].
  apply (st_ok_pi_add_region _ _ _
  (YP09.mkRegion (Some 11%nat) 24 32 0 0 [YP09.mkChunk 24 (CVal 8 (SOff 33 0))])) in HS;
  [ | vm_compute; reflexivity | | ].
  + assert (SHOKW : sh_ok SEGS CWA_BX [mkSHE 11 24 32] E (mrestrict (w_H W) (ms_mem ms))).
    { unfold sh_ok. constructor; [|constructor].
      apply (shent_ok_of_range SEGS (w_H W) (ms_mem ms) E CWA_BX 11 qb (req_size kb) wp 24 32).
      + exact HRAW.
      + unfold U, CWA_BX. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Usb.
      + unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact BW.
      + lia.
      + lia.
      + intros x Hx. cbn [Z.min Z.max] in Hx.
        unfold in_app, kLowShadowBeg, kHighMemBeg in Hbia. destruct Hbia as [_ [Hap | [Hap Hap2]]];
        cwa_unf; lia. }
    clear SHOK. rename SHOKW into SHOK.
    paj_run_tok RUN HS HJ SHOK CWA_SPAN; [awr_ok_tac; exact Esp |].
    lazymatch goal with |- SRr _ _ (mkCfg _ ?mdq) _ => set (mdv2 := mdq) in *; clearbody mdv2 end.
    (* the memory at the first call *)
    assert (K2 : kept_out (rdW W (ms_mem ms)) (rdW W (ms_mem ms0)) (spZ regs - 64) (spZ regs)).
    { apply (cwh_mem_kept _ W _ _ _ _ _ HFr).
      intros b wlo whi a Hin Hr'.
      cbv [windows] in Hin. cbn [map In YP09.r_base YP09.r_wlo YP09.r_whi] in Hin.
      repeat (destruct Hin as [Heq | Hin];
              [inversion Heq; subst; cbn [base_val] in Hr'; rewrite ?Esp in Hr'; lia |]);
      destruct Hin. }
    assert (K12 : kept_out (rdW W mem) (rdW W (ms_mem ms0)) (spZ regs - 64) (spZ regs))
    by (exact (kept_out_trans _ _ _ _ _ _ _ K1 K2 ltac:(lia) ltac:(lia))).
    assert (ROKc : cmd_ro_ok (rdW W (ms_mem ms0)))
    by (exact (cwh_ro_kept _ _ _ _ K12 ltac:(cwa_unf; lia) ltac:(cwa_unf; lia) HROK)).
    assert (AP3c : cwa_str B ly S (rdW W (ms_mem ms0)) p3 w3)
    by (exact (cwh_argA_kept ly S W regs mem md (ms_mem ms0) _ _ p3 w3 HAR0 Hsp2 AP3 K12
        ltac:(cwa_unf; lia) ltac:(cwa_unf; lia))).
    clear HF HFr HG.
    (* the registers at the call *)
    pmkst HS.
    prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
    prreg HS (4%bv : bv 5) Q4. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
    assert (Qsp : spZ (ms_regs ms0) = spZ regs + (-64)).
    { unfold spZ in *. rewrite Q2, Esp. apply unsigned_lit_small. cwa_unf; lia. }
    assert (Qgp : getr (ms_regs ms0) 3 = w64 (as_gp B))
    by (rewrite Q3, (EN 3%nat 3%bv ltac:(lia) eq_refl); exact Hgp).
    assert (Qtp : getr (ms_regs ms0) 4 = w64 (as_tp B))
    by (rewrite Q4, (EN 4%nat 4%bv ltac:(lia) eq_refl); exact Htp).
    assert (Qra : YK0s.ret_ok (getr (ms_regs ms0) 1))
    by (rewrite Q1; apply ret_ok_codeptr_v; [cbv; split; [congruence | reflexivity] | reflexivity]).
    assert (Qa0 : getr (ms_regs ms0) 10 = w64 p3) by (rewrite Q10, Ea33; reflexivity).
    assert (Ea271 : ew E 271 = Z_to_bv 64 (VAL (A_OBJ 30)))
    by (unfold E, cwa_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
    assert (VO30 : VAL (A_OBJ 30) = 0x21b20)
    by (rewrite (VOBJS 30%nat ltac:(vm_compute; lia)); vm_compute; reflexivity).
    assert (Qa1 : getr (ms_regs ms0) 11 = w64 0x21b20)
    by (rewrite Q11, Ea271, VO30; reflexivity).
    assert (Hspc : alloc_ceiling <= spZ (ms_regs ms0) - 2 * ESTACK) by (rewrite Qsp; cwa_unf; lia).
    (* the two strings the entry compares *)
    destruct (cwa_str_facts B ly S W (ms_regs ms0) (ms_mem ms0) mdv2 p3 w3
    (proj1 HJ) AP3c Hspc) as (_ & SP3c & RP3c & TP3c & _ & _).
    assert (HBown : abytes_atR (rdW W (ms_mem ms0)) 0x21b20 RO_lit_21b20)
    by (destruct ROKc as [HROB _]; unfold cmd_ro_bytes in HROB;
        repeat (destruct HROB as [? HROB]); assumption).
    destruct (cwh_lit_str ly S W (ms_regs ms0) (ms_mem ms0) mdv2 0x21b20 4 RO_lit_21b20 S_OWN
    (proj1 HJ) ROKc Hspc ltac:(cbv [CWA_LITS In]; tauto) HBown
    ltac:(cbv [cmd_ro_ends In]; tauto) ltac:(vm_compute; reflexivity)
    ltac:(apply notin_nul_lit; vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
    as (SOWN & ROWN & TOWN).
    assert (HEP : ecall_pre_stk SEGS B (2 * ESTACK) ly S W (ms_regs ms0) (ms_mem ms0) mdv2).
    { eapply (ecall_pre_stk_at SEGS B
      (2 * ESTACK) CHECK_WORDS_ADD_STK (spZ regs) [] ly S W mem md [] ly S W (ms_mem ms0) _ 0
      (ms_regs ms0) (-64) HJ Qsp);
      [reflexivity | lia | unfold ESTACK; lia | unfold CHECK_WORDS_ADD_STK, ESTACK; lia
      | exact Qra | exact Qgp | exact Qtp]. }
    assert (ROMc : rt_rom_view SEGS B W (ms_mem ms0))
    by (eapply (cwa_rom_at B RLO RHI); [exact HRO | exact HJ]).
    assert (HC : SRr SEGS W
    (cfg_at SEGS (SIGMA CS___interceptor_trampoline_strcmp) (ms_regs ms0) (ms_mem ms0) mdv2)
    (art_post SEGS B (2 * ESTACK) ly S W (ms_regs ms0) (ms_mem ms0) mdv2
    (fun _ => False) (fun regs' _ => getr regs' 10 = w64 0 <-> w3 = S_OWN)))
    by (exact (ASTRCMP ly S W (ms_regs ms0) (ms_mem ms0) mdv2 p3 0x21b20 w3 S_OWN
    HEP Qa0 Qa1 ltac:(lia) ltac:(lia) SP3c SOWN RP3c ROWN TP3c TOWN ROMc)).
    eapply SRr_bind.
    { exact (aj_art_at SEGS B (cwa_laws B) Hsegs (cf_env B HFACTS) (2 * ESTACK)
      (fun _ => False) (SIGMA CS___interceptor_trampoline_strcmp) W (ms_regs ms0) (ms_mem ms0)
      CHECK_WORDS_ADD_STK (spZ regs) [] ly S W mem md [] ly S mdv2 0 (-64) (getr (ms_regs ms0) 1)
      (fun regs' _ => getr regs' 10 = w64 0 <-> w3 = S_OWN)
      HJ Qsp ltac:(reflexivity) ltac:(lia) ltac:(unfold ESTACK; lia)
      ltac:(unfold CHECK_WORDS_ADD_STK, ESTACK; lia)
      eq_refl (fun a H => False_ind _ H) HC). }
    cbv beta. intros W2 c2 _ (HW2 & regs2 & mem2 & md2 & Hc2 & HJ2 & HP2 & HQr2 & HKP2). subst W2 c2.
    rewrite Q1.
    pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _ & _ & _).
    jafter_call_keep_pi HS 52%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2; 3]%nat HS2.
    match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
    { cbn [ms_mem restrict].
      repeat apply Forall_cons; try apply Forall_nil;
      cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi].
      - apply (cwa_region_kept _ W (ms_mem ms0) mem2 _ (spZ regs + -64 - 2 * ESTACK) (spZ regs + -64));
        [ intros a Ha Hn; exact (HKP2 a Ha Hn (fun x => x)) | .. ];
        cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi];
        rewrite ?BW; cwa_unf; lia.
      - apply (cwh_region_kept_w _ W (ms_mem ms0) mem2 _ (spZ regs + -64 - 2 * ESTACK) (spZ regs + -64));
        [ intros a Ha Hn; exact (HKP2 a Ha Hn (fun x => x)) | .. ];
        cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi];
        rewrite ?Esp; try (cwa_unf; lia).
        intros a Ha. apply Hpres2. cwa_unf; lia.
      - apply (cwa_region_kept _ W (ms_mem ms0) mem2 _ (spZ regs + -64 - 2 * ESTACK) (spZ regs + -64));
        [ intros a Ha Hn; exact (HKP2 a Ha Hn (fun x => x)) | .. ];
        cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi];
        rewrite ?BG; cwa_unf; lia.
      - apply (cwa_region_kept _ W (ms_mem ms0) mem2 _ (spZ regs + -64 - 2 * ESTACK) (spZ regs + -64));
        [ intros a Ha Hn; exact (HKP2 a Ha Hn (fun x => x)) | .. ];
        cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi];
        rewrite ?BC; cwa_unf; lia. }
    clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
    lazymatch type of HS with st_ok_pi _ _ ?Eh _ _ =>
    assert (HEIh : img_env VAL A_LIM Eh) by (apply img_env_havoc; [exact HEI | cbv; lia]) end.
    (* the first answer: 0 exactly when word 3 is "own" *)
    lazymatch type of HS with st_ok_pi _ _ ?Eh _ _ =>
    assert (ENh : forall (n : nat) (rr : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned rr ->
    ew Eh n = getr regs rr)
    by (intros n rr Hn Hrr; rewrite !ew_havoc_old by lia; exact (EN n rr Hn Hrr));
    assert (Esph : bv_unsigned (ew Eh 2) = spZ regs)
    by (rewrite !ew_havoc_old by lia; exact Esp);
    assert (Ea33h : ew Eh 33 = Z_to_bv 64 p3)
    by (rewrite !ew_havoc_old by lia; exact Ea33);
    assert (Ea32h : ew Eh 32 = Z_to_bv 64 SHADOW_OFF)
    by (rewrite !ew_havoc_old by lia; exact Ea32);
    assert (Ea56h : ew Eh 56 = getr regs2 10)
    by (cbn [ew havoc nth map CLOB Nat.ltb Nat.sub]; reflexivity);
    assert (SHOK2 : sh_ok SEGS CWA_BX [] Eh (mrestrict (w_H W) mem2))
    by constructor end.
    lazymatch type of HS with st_ok_pi _ _ ?Eh _ _ =>
    assert (HU56 : U Eh (SOff 56 0) = bv_unsigned (getr regs2 10))
    by (unfold U; cbn [sv_denot]; rewrite Ea56h, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity);
    assert (HU0 : U Eh (SLit 0) = 0)
    by (unfold U; cbn [sv_denot]; apply unsigned_lit_small; lia) end.
    psrr_branch_tok RUN BR HS SHOK2 CWA_SPAN.
    * (* word 3 is "own": the placement is word 3 *)
      rewrite branch_eq_U, HU56, HU0 in Hc. apply Z.eqb_eq in Hc.
      assert (HW3 : w3 = S_OWN) by (apply (proj1 HQr2); apply cwh_zero_iff; exact Hc).
      assert (HPL : PCwa.is_placement_b w3 = true)
      by (rewrite HW3; vm_compute; reflexivity).
      assert (KC : kept_out (rdW W (ms_mem ms0)) (rdW W mem2)
      (spZ regs - 64 - 2 * ESTACK) (spZ regs))
      by (intros a Ha Hn; exact (HKP2 a Ha ltac:(cwa_unf; lia) (fun x => x))).
      assert (K12w : kept_out (rdW W mem) (rdW W (ms_mem ms0))
      (spZ regs - 64 - 2 * ESTACK) (spZ regs)).
      { apply (cwh_kept_wide _ _ (spZ regs - 64) (spZ regs)); [exact K12 | cwa_unf; lia | lia]. }
      assert (K13 : kept_out (rdW W mem) (rdW W mem2) (spZ regs - 64 - 2 * ESTACK) (spZ regs))
      by (exact (kept_out_trans _ _ _ _ _ _ _ K12w KC ltac:(lia) ltac:(lia))).
      paj_run_to_tok RUNTO HS HJ2 SHOK2 CWA_SPAN 0x2a34; [awr_ok_tac; exact Esph |].
      lazymatch goal with |- SRr _ _ (mkCfg _ ?mdq) _ => set (mdv3 := mdq) in *; clearbody mdv3 end.
      assert (K4 : kept_out (rdW W mem2) (rdW W (ms_mem ms1)) (spZ regs - 64) (spZ regs)).
      { apply (cwh_mem_kept _ W _ _ _ _ _ HFr).
        intros b wlo whi a Hin Hr'.
        cbv [windows] in Hin. cbn [map In YP09.r_base YP09.r_wlo YP09.r_whi] in Hin.
        repeat (destruct Hin as [Heq | Hin];
                [inversion Heq; subst; cbn [base_val] in Hr'; rewrite ?Esph in Hr'; lia |]);
        destruct Hin. }
      assert (K4w : kept_out (rdW W mem2) (rdW W (ms_mem ms1))
      (spZ regs - 64 - 2 * ESTACK) (spZ regs)).
      { apply (cwh_kept_wide _ _ (spZ regs - 64) (spZ regs)); [exact K4 | cwa_unf; lia | lia]. }
      assert (KF : kept_out (rdW W mem) (rdW W (ms_mem ms1))
      (spZ regs - 64 - 2 * ESTACK) (spZ regs))
      by (exact (kept_out_trans _ _ _ _ _ _ _ K13 K4w ltac:(lia) ltac:(lia))).
      (* what the join lemma reads *)
      assert (ROKf : cmd_ro_ok (rdW W (ms_mem ms1)))
      by (exact (cwh_ro_kept _ _ _ _ KF ltac:(cwa_unf; lia) ltac:(cwa_unf; lia) HROK)).
      assert (HNf : aval_mem (rdW W (ms_mem ms1)) (cp + CALL_OFF_NARGS) 4 4)
      by (exact (cwh_val_kept W mem (ms_mem ms1) _ _ _ 4%nat 4 KF HN
          ltac:(cwh_unf; lia) ltac:(cwh_unf; lia) ltac:(cwa_unf; lia))).
      assert (HQ2f : aval_mem (rdW W (ms_mem ms1)) (cp + CALL_OFF_ARGS + 16) 8 q2)
      by (exact (cwh_val_kept W mem (ms_mem ms1) _ _ _ 8%nat q2 KF HV2
          ltac:(cwh_unf; lia) ltac:(cwh_unf; lia) ltac:(cwa_unf; lia))).
      assert (HQ3f : aval_mem (rdW W (ms_mem ms1)) (cp + CALL_OFF_ARGS + 24) 8 q3)
      by (exact (cwh_val_kept W mem (ms_mem ms1) _ _ _ 8%nat q3 KF HV3
          ltac:(cwh_unf; lia) ltac:(cwh_unf; lia) ltac:(cwa_unf; lia))).
      assert (HX2W : x2 = w3)
      by (rewrite HX2; exact (proj1 (cwh_client_word r w3 w4 ltac:(lia) HPL))).
      assert (AQ2f : cwa_str B ly S (rdW W (ms_mem ms1)) q2 w3).
      { rewrite <- HX2W.
        exact (cwh_argA_kept ly S W regs mem md (ms_mem ms1) _ _ q2 x2 HAR0 Hsp2 AQ2 KF
        ltac:(cwa_unf; lia) ltac:(cwa_unf; lia)). }
      assert (AQ3f : cwa_str B ly S (rdW W (ms_mem ms1)) q3 x3)
      by (exact (cwh_argA_kept ly S W regs mem md (ms_mem ms1) _ _ q3 x3 HAR0 Hsp2 AQ3 KF
          ltac:(cwa_unf; lia) ltac:(cwa_unf; lia))).
      assert (AP3f : cwa_str B ly S (rdW W (ms_mem ms1)) p3 w3)
      by (exact (cwh_argA_kept ly S W regs mem md (ms_mem ms1) _ _ p3 w3 HAR0 Hsp2 AP3 KF
          ltac:(cwa_unf; lia) ltac:(cwa_unf; lia))).
      assert (AW4f : 4 < r -> in_blockA (ablocks B ly S) (wp + 32) 8 /\
      aval_mem (rdW W (ms_mem ms1)) (wp + 32) 8 p4 /\
      cwa_str B ly S (rdW W (ms_mem ms1)) p4 w4).
      { intros H4. destruct (AW4 H4) as (HB4 & HV4 & AP4).
        pose proof HB4 as (qc & kc & Hinc & Hqc1 & Hqc2).
        destruct (al_blocks _ _ (cwa_laws B) _ _ _ _ _ qc kc HAR0 Hinc)
        as (_ & Hc4096 & Hcceil & _ & _ & _).
        pose proof (req_size_pos kc ltac:(lia)) as [Hkc1 Hkc2].
        split; [exact HB4|]. split.
        - exact (cwh_val_kept W mem (ms_mem ms1) _ _ _ 8%nat p4 KF HV4
          ltac:(cwa_unf; lia) ltac:(cwa_unf; lia) ltac:(cwa_unf; lia)).
        - exact (cwh_argA_kept ly S W regs mem md (ms_mem ms1) _ _ p4 w4 HAR0 Hsp2 AP4 KF
          ltac:(cwa_unf; lia) ltac:(cwa_unf; lia)). }
      assert (HXW : x3 = (if 4 <? r then w4 else S_DASH))
      by (rewrite HX3; exact (proj2 (cwh_client_word r w3 w4 ltac:(lia) HPL))).
      (* the frame and the registers at the join *)
      assert (HFRM : cwa_frame (mrestrict (w_H W) (ms_mem ms1)) (spZ regs) regs).
      { pose proof (st_ok_region_nth (segs := SEGS) _ _ _ 1%nat _ HS eq_refl) as HRG.
        cbn [ms_mem restrict] in HRG.
        exact (cwh_frame_all _ W _ (spZ regs) regs HRG Esph ENh). }
      pmkst HS.
      prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
      prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18.
      prreg HS (19%bv : bv 5) P19. prreg HS (21%bv : bv 5) P21.
      assert (T2 : getr (ms_regs ms1) 2 = w64 (spZ regs - 64))
      by (rewrite P2, Esp; unfold w64; f_equal; lia).
      assert (T3 : getr (ms_regs ms1) 3 = getr regs 3)
      by (rewrite P3; exact (EN 3%nat 3%bv ltac:(lia) eq_refl)).
      assert (T4 : getr (ms_regs ms1) 4 = getr regs 4)
      by (rewrite P4; exact (EN 4%nat 4%bv ltac:(lia) eq_refl)).
      assert (T8 : getr (ms_regs ms1) 8 = w64 cp)
      by (rewrite P8, (EN 10%nat 10%bv ltac:(lia) eq_refl); exact R10).
      assert (T9 : getr (ms_regs ms1) 9 = w64 p3) by (rewrite P9, Ea33; reflexivity).
      assert (T18 : getr (ms_regs ms1) 18 = w64 wp)
      by (rewrite P18, (EN 11%nat 11%bv ltac:(lia) eq_refl); exact R11).
      assert (T19 : getr (ms_regs ms1) 19 = w64 r)
      by (rewrite P19, (EN 12%nat 12%bv ltac:(lia) eq_refl); exact R12).
      assert (T21 : getr (ms_regs ms1) 21 = w64 SHADOW_OFF)
      by (rewrite P21, Ea32; reflexivity).
      assert (Thi : forall rr, 22 <= rr <= 27 ->
      getr (ms_regs ms1) (Z_to_bv 5 rr) = getr regs (Z_to_bv 5 rr)).
      { intros rr Hrr.
        assert (Hc' : rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia.
        repeat (destruct Hc' as [-> | Hc']); [..|subst rr];
        lazymatch goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
          let G := fresh "G" in prreg HS (Z_to_bv 5 k) G; rewrite G end;
        lazymatch goal with |- ew _ ?n = getr _ ?r2 =>
          exact (EN n r2 ltac:(lia) eq_refl) end. }
      exact (cwa_mid_word B RLO RHI HFACTS ly S W regs mem md cp q2 q3 wp r p3 p4 x3 w3 w4
      (ms_mem ms1) mdv3 (ms_regs ms1) HPRE HRO HJ2 VOBJS ASTRCMP ROKf T2 T3 T4 Thi T8 T9 T18 T19 T21
      ltac:(lia) HFRM Hcp1 Hcp2 Hcp8 Hwp8 HNf HQ2f HQ3f AQ2f AQ3f AP3f HPL AW4f HXW).
    * (* word 3 is not "own": the second wrapper call, against "default" *)
      rewrite branch_eq_U, HU56, HU0 in Hc. apply Z.eqb_neq in Hc.
      assert (HNOWN : bytes_eqb w3 S_OWN = false).
      { destruct (bytes_eqb w3 S_OWN) eqn:Eq; [|reflexivity]. exfalso.
        apply Hc. apply cwh_zero_iff. apply (proj2 HQr2). apply bytes_eqb_iff. exact Eq. }
      assert (KC : kept_out (rdW W (ms_mem ms0)) (rdW W mem2)
      (spZ regs - 64 - 2 * ESTACK) (spZ regs))
      by (intros a Ha Hn; exact (HKP2 a Ha ltac:(cwa_unf; lia) (fun x => x))).
      assert (K12w : kept_out (rdW W mem) (rdW W (ms_mem ms0))
      (spZ regs - 64 - 2 * ESTACK) (spZ regs)).
      { apply (cwh_kept_wide _ _ (spZ regs - 64) (spZ regs)); [exact K12 | cwa_unf; lia | lia]. }
      assert (K13 : kept_out (rdW W mem) (rdW W mem2) (spZ regs - 64 - 2 * ESTACK) (spZ regs))
      by (exact (kept_out_trans _ _ _ _ _ _ _ K12w KC ltac:(lia) ltac:(lia))).
      clear HKP2 KC K12w K12 K1 K2.
      paj_run_tok RUN HS HJ2 SHOK2 CWA_SPAN; [awr_ok_tac; exact Esph |].
      lazymatch goal with |- SRr _ _ (mkCfg _ ?mdq) _ => set (mdv3 := mdq) in *; clearbody mdv3 end.
      assert (K4 : kept_out (rdW W mem2) (rdW W (ms_mem ms1)) (spZ regs - 64) (spZ regs)).
      { apply (cwh_mem_kept _ W _ _ _ _ _ HFr).
        intros b wlo whi a Hin Hr'.
        cbv [windows] in Hin. cbn [map In YP09.r_base YP09.r_wlo YP09.r_whi] in Hin.
        repeat (destruct Hin as [Heq | Hin];
                [inversion Heq; subst; cbn [base_val] in Hr'; rewrite ?Esph in Hr'; lia |]);
        destruct Hin. }
      assert (K4w : kept_out (rdW W mem2) (rdW W (ms_mem ms1))
      (spZ regs - 64 - 2 * ESTACK) (spZ regs)).
      { apply (cwh_kept_wide _ _ (spZ regs - 64) (spZ regs)); [exact K4 | cwa_unf; lia | lia]. }
      assert (K14 : kept_out (rdW W mem) (rdW W (ms_mem ms1))
      (spZ regs - 64 - 2 * ESTACK) (spZ regs))
      by (exact (kept_out_trans _ _ _ _ _ _ _ K13 K4w ltac:(lia) ltac:(lia))).
      clear HF HFr HG K4 K4w Q1 Q2 Q3 Q4 Q10 Q11 Qsp Qgp Qtp Qra Qa0 Qa1 Hspc HEP ROMc HC
      SP3c RP3c TP3c SOWN ROWN TOWN HBown.
      assert (ROKd : cmd_ro_ok (rdW W (ms_mem ms1)))
      by (exact (cwh_ro_kept _ _ _ _ K14 ltac:(cwa_unf; lia) ltac:(cwa_unf; lia) HROK)).
      assert (AP3d : cwa_str B ly S (rdW W (ms_mem ms1)) p3 w3)
      by (exact (cwh_argA_kept ly S W regs mem md (ms_mem ms1) _ _ p3 w3 HAR0 Hsp2 AP3 K14
          ltac:(cwa_unf; lia) ltac:(cwa_unf; lia))).
      pmkst HS.
      prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
      prreg HS (4%bv : bv 5) Q4. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
      assert (Qsp : spZ (ms_regs ms1) = spZ regs + (-64)).
      { unfold spZ in *. rewrite Q2, Esp. apply unsigned_lit_small. cwa_unf; lia. }
      assert (Qgp : getr (ms_regs ms1) 3 = w64 (as_gp B))
      by (rewrite Q3, (EN 3%nat 3%bv ltac:(lia) eq_refl); exact Hgp).
      assert (Qtp : getr (ms_regs ms1) 4 = w64 (as_tp B))
      by (rewrite Q4, (EN 4%nat 4%bv ltac:(lia) eq_refl); exact Htp).
      assert (Qra : YK0s.ret_ok (getr (ms_regs ms1) 1))
      by (rewrite Q1; apply ret_ok_codeptr_v; [cbv; split; [congruence | reflexivity] | reflexivity]).
      assert (Qa0 : getr (ms_regs ms1) 10 = w64 p3) by (rewrite Q10, Ea33; reflexivity).
      assert (Ea272 : ew E 272 = Z_to_bv 64 (VAL (A_OBJ 31)))
      by (unfold E, cwa_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
      assert (VO31 : VAL (A_OBJ 31) = 0x21b40)
      by (rewrite (VOBJS 31%nat ltac:(vm_compute; lia)); vm_compute; reflexivity).
      assert (Qa1 : getr (ms_regs ms1) 11 = w64 0x21b40)
      by (rewrite Q11, Ea272, VO31; reflexivity).
      assert (Hspd : alloc_ceiling <= spZ (ms_regs ms1) - 2 * ESTACK) by (rewrite Qsp; cwa_unf; lia).
      destruct (cwa_str_facts B ly S W (ms_regs ms1) (ms_mem ms1) mdv3 p3 w3
      (proj1 HJ2) AP3d Hspd) as (_ & SP3d & RP3d & TP3d & _ & _).
      assert (HBdef : abytes_atR (rdW W (ms_mem ms1)) 0x21b40 RO_lit_21b40)
      by (destruct ROKd as [HROB _]; unfold cmd_ro_bytes in HROB;
          repeat (destruct HROB as [? HROB]); assumption).
      destruct (cwh_lit_str ly S W (ms_regs ms1) (ms_mem ms1) mdv3 0x21b40 8 RO_lit_21b40 S_DEFAULT
      (proj1 HJ2) ROKd Hspd ltac:(cbv [CWA_LITS In]; tauto) HBdef
      ltac:(cbv [cmd_ro_ends In]; tauto) ltac:(vm_compute; reflexivity)
      ltac:(apply notin_nul_lit; vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
      as (SDEF & RDEF & TDEF).
      assert (HEP : ecall_pre_stk SEGS B (2 * ESTACK) ly S W (ms_regs ms1) (ms_mem ms1) mdv3).
      { eapply (ecall_pre_stk_at SEGS B
        (2 * ESTACK) CHECK_WORDS_ADD_STK (spZ regs) [] ly S W mem md [] ly S W (ms_mem ms1) _ 0
        (ms_regs ms1) (-64) HJ2 Qsp);
        [reflexivity | lia | unfold ESTACK; lia | unfold CHECK_WORDS_ADD_STK, ESTACK; lia
        | exact Qra | exact Qgp | exact Qtp]. }
      assert (ROMd : rt_rom_view SEGS B W (ms_mem ms1))
      by (eapply (cwa_rom_at B RLO RHI); [exact HRO | exact HJ2]).
      assert (HC : SRr SEGS W
      (cfg_at SEGS (SIGMA CS___interceptor_trampoline_strcmp) (ms_regs ms1) (ms_mem ms1) mdv3)
      (art_post SEGS B (2 * ESTACK) ly S W (ms_regs ms1) (ms_mem ms1) mdv3
      (fun _ => False) (fun regs' _ => getr regs' 10 = w64 0 <-> w3 = S_DEFAULT)))
      by (exact (ASTRCMP ly S W (ms_regs ms1) (ms_mem ms1) mdv3 p3 0x21b40 w3 S_DEFAULT
      HEP Qa0 Qa1 ltac:(lia) ltac:(lia) SP3d SDEF RP3d RDEF TP3d TDEF ROMd)).
      eapply SRr_bind.
      { exact (aj_art_at SEGS B (cwa_laws B) Hsegs (cf_env B HFACTS) (2 * ESTACK)
        (fun _ => False) (SIGMA CS___interceptor_trampoline_strcmp) W (ms_regs ms1) (ms_mem ms1)
        CHECK_WORDS_ADD_STK (spZ regs) [] ly S W mem md [] ly S mdv3 0 (-64) (getr (ms_regs ms1) 1)
        (fun regs' _ => getr regs' 10 = w64 0 <-> w3 = S_DEFAULT)
        HJ2 Qsp ltac:(reflexivity) ltac:(lia) ltac:(unfold ESTACK; lia)
        ltac:(unfold CHECK_WORDS_ADD_STK, ESTACK; lia)
        eq_refl (fun a H => False_ind _ H) HC). }
      cbv beta. intros W3 c3 _ (HW3 & regs3 & mem3 & md3 & Hc3 & HJ3 & HP3 & HQr3 & HKP3).
      subst W3 c3.
      rewrite Q1.
      pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3 & _ & _ & _).
      jafter_call_keep_pi HS 80%nat regs3 (mrestrict (w_H W) mem3) HP3 [0; 1; 2; 3]%nat HS3.
      match type of HS3 with ?t -> _ => assert (HRK : t); [|specialize (HS3 HRK); clear HRK] end.
      { cbn [ms_mem restrict].
        repeat apply Forall_cons; try apply Forall_nil;
        cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi].
        - apply (cwa_region_kept _ W (ms_mem ms1) mem3 _
          (spZ regs + -64 - 2 * ESTACK) (spZ regs + -64));
          [ intros a Ha Hn; exact (HKP3 a Ha Hn (fun x => x)) | .. ];
          cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi];
          cbn [ew havoc nth map CLOB Nat.ltb Nat.leb Nat.sub];
          rewrite ?BW; cwa_unf; lia.
        - apply (cwh_region_kept_w _ W (ms_mem ms1) mem3 _
          (spZ regs + -64 - 2 * ESTACK) (spZ regs + -64));
          [ intros a Ha Hn; exact (HKP3 a Ha Hn (fun x => x)) | .. ];
          cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi];
          cbn [ew havoc nth map CLOB Nat.ltb Nat.leb Nat.sub];
          rewrite ?Esp; try (cwa_unf; lia).
          intros a Ha. apply Hpres3. cwa_unf; lia.
        - apply (cwa_region_kept _ W (ms_mem ms1) mem3 _
          (spZ regs + -64 - 2 * ESTACK) (spZ regs + -64));
          [ intros a Ha Hn; exact (HKP3 a Ha Hn (fun x => x)) | .. ];
          cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi];
          cbn [ew havoc nth map CLOB Nat.ltb Nat.leb Nat.sub];
          rewrite ?BG; cwa_unf; lia.
        - apply (cwa_region_kept _ W (ms_mem ms1) mem3 _
          (spZ regs + -64 - 2 * ESTACK) (spZ regs + -64));
          [ intros a Ha Hn; exact (HKP3 a Ha Hn (fun x => x)) | .. ];
          cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi];
          cbn [ew havoc nth map CLOB Nat.ltb Nat.leb Nat.sub];
          rewrite ?BC; cwa_unf; lia. }
      clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
      clear HEIh ENh Esph Ea33h Ea32h Ea56h HU56 HU0 SHOK2.
      lazymatch type of HS with st_ok_pi _ _ ?Eh _ _ =>
      assert (HEIh : img_env VAL A_LIM Eh) by (apply img_env_havoc; [assumption | cbv; lia]);
      assert (ENh : forall (n : nat) (rr : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned rr ->
      ew Eh n = getr regs rr)
      by (intros n rr Hn Hrr; rewrite !ew_havoc_old by lia; exact (EN n rr Hn Hrr));
      assert (Esph : bv_unsigned (ew Eh 2) = spZ regs)
      by (rewrite !ew_havoc_old by lia; exact Esp);
      assert (Ea33h : ew Eh 33 = Z_to_bv 64 p3)
      by (rewrite !ew_havoc_old by lia; exact Ea33);
      assert (Ea32h : ew Eh 32 = Z_to_bv 64 SHADOW_OFF)
      by (rewrite !ew_havoc_old by lia; exact Ea32);
      assert (Ea84h : ew Eh 84 = getr regs3 10)
      by (cbn [ew havoc nth map CLOB Nat.ltb Nat.sub]; reflexivity);
      assert (SHOK2 : sh_ok SEGS CWA_BX [] Eh (mrestrict (w_H W) mem3)) by constructor;
      assert (HU84 : U Eh (SOff 84 0) = bv_unsigned (getr regs3 10))
      by (unfold U; cbn [sv_denot]; rewrite Ea84h, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity);
      assert (HU0 : U Eh (SLit 0) = 0)
      by (unfold U; cbn [sv_denot]; apply unsigned_lit_small; lia) end.
      assert (KC2 : kept_out (rdW W (ms_mem ms1)) (rdW W mem3)
      (spZ regs - 64 - 2 * ESTACK) (spZ regs))
      by (intros a Ha Hn; exact (HKP3 a Ha ltac:(cwa_unf; lia) (fun x => x))).
      assert (K15 : kept_out (rdW W mem) (rdW W mem3) (spZ regs - 64 - 2 * ESTACK) (spZ regs))
      by (exact (kept_out_trans _ _ _ _ _ _ _ K14 KC2 ltac:(lia) ltac:(lia))).
      psrr_branch_tok RUN BR HS SHOK2 CWA_SPAN.
      -- (* word 3 is "default" *)
         rewrite branch_eq_U, HU84, HU0 in Hc0. apply Z.eqb_eq in Hc0.
         assert (HW3d : w3 = S_DEFAULT)
         by (apply (proj1 HQr3); apply cwh_zero_iff; exact Hc0).
         assert (HPL : PCwa.is_placement_b w3 = true)
         by (rewrite HW3d; vm_compute; reflexivity).
         paj_run_to_tok RUNTO HS HJ3 SHOK2 CWA_SPAN 0x2a34; [awr_ok_tac; exact Esph |].
         lazymatch goal with |- SRr _ _ (mkCfg _ ?mdq) _ =>
           set (mdv4 := mdq) in *; clearbody mdv4 end.
         assert (K5 : kept_out (rdW W mem3) (rdW W (ms_mem ms2)) (spZ regs - 64) (spZ regs)).
         { apply (cwh_mem_kept _ W _ _ _ _ _ HFr).
           intros b wlo whi a Hin Hr'.
           cbv [windows] in Hin. cbn [map In YP09.r_base YP09.r_wlo YP09.r_whi] in Hin.
           repeat (destruct Hin as [Heq | Hin];
                   [inversion Heq; subst; cbn [base_val] in Hr'; rewrite ?Esph in Hr'; lia |]);
           destruct Hin. }
         assert (K5w : kept_out (rdW W mem3) (rdW W (ms_mem ms2))
         (spZ regs - 64 - 2 * ESTACK) (spZ regs)).
         { apply (cwh_kept_wide _ _ (spZ regs - 64) (spZ regs)); [exact K5 | cwa_unf; lia | lia]. }
         assert (KF : kept_out (rdW W mem) (rdW W (ms_mem ms2))
         (spZ regs - 64 - 2 * ESTACK) (spZ regs))
         by (exact (kept_out_trans _ _ _ _ _ _ _ K15 K5w ltac:(lia) ltac:(lia))).
         assert (ROKf : cmd_ro_ok (rdW W (ms_mem ms2)))
         by (exact (cwh_ro_kept _ _ _ _ KF ltac:(cwa_unf; lia) ltac:(cwa_unf; lia) HROK)).
         assert (HNf : aval_mem (rdW W (ms_mem ms2)) (cp + CALL_OFF_NARGS) 4 4)
         by (exact (cwh_val_kept W mem (ms_mem ms2) _ _ _ 4%nat 4 KF HN
             ltac:(cwh_unf; lia) ltac:(cwh_unf; lia) ltac:(cwa_unf; lia))).
         assert (HQ2f : aval_mem (rdW W (ms_mem ms2)) (cp + CALL_OFF_ARGS + 16) 8 q2)
         by (exact (cwh_val_kept W mem (ms_mem ms2) _ _ _ 8%nat q2 KF HV2
             ltac:(cwh_unf; lia) ltac:(cwh_unf; lia) ltac:(cwa_unf; lia))).
         assert (HQ3f : aval_mem (rdW W (ms_mem ms2)) (cp + CALL_OFF_ARGS + 24) 8 q3)
         by (exact (cwh_val_kept W mem (ms_mem ms2) _ _ _ 8%nat q3 KF HV3
             ltac:(cwh_unf; lia) ltac:(cwh_unf; lia) ltac:(cwa_unf; lia))).
         assert (HX2W : x2 = w3)
         by (rewrite HX2; exact (proj1 (cwh_client_word r w3 w4 ltac:(lia) HPL))).
         assert (AQ2f : cwa_str B ly S (rdW W (ms_mem ms2)) q2 w3).
         { rewrite <- HX2W.
           exact (cwh_argA_kept ly S W regs mem md (ms_mem ms2) _ _ q2 x2 HAR0 Hsp2 AQ2 KF
           ltac:(cwa_unf; lia) ltac:(cwa_unf; lia)). }
         assert (AQ3f : cwa_str B ly S (rdW W (ms_mem ms2)) q3 x3)
         by (exact (cwh_argA_kept ly S W regs mem md (ms_mem ms2) _ _ q3 x3 HAR0 Hsp2 AQ3 KF
             ltac:(cwa_unf; lia) ltac:(cwa_unf; lia))).
         assert (AP3f : cwa_str B ly S (rdW W (ms_mem ms2)) p3 w3)
         by (exact (cwh_argA_kept ly S W regs mem md (ms_mem ms2) _ _ p3 w3 HAR0 Hsp2 AP3 KF
             ltac:(cwa_unf; lia) ltac:(cwa_unf; lia))).
         assert (AW4f : 4 < r -> in_blockA (ablocks B ly S) (wp + 32) 8 /\
         aval_mem (rdW W (ms_mem ms2)) (wp + 32) 8 p4 /\
         cwa_str B ly S (rdW W (ms_mem ms2)) p4 w4).
         { intros H4. destruct (AW4 H4) as (HB4 & HV4 & AP4).
           pose proof HB4 as (qc & kc & Hinc & Hqc1 & Hqc2).
           destruct (al_blocks _ _ (cwa_laws B) _ _ _ _ _ qc kc HAR0 Hinc)
           as (_ & Hc4096 & Hcceil & _ & _ & _).
           pose proof (req_size_pos kc ltac:(lia)) as [Hkc1 Hkc2].
           split; [exact HB4|]. split.
           - exact (cwh_val_kept W mem (ms_mem ms2) _ _ _ 8%nat p4 KF HV4
             ltac:(cwa_unf; lia) ltac:(cwa_unf; lia) ltac:(cwa_unf; lia)).
           - exact (cwh_argA_kept ly S W regs mem md (ms_mem ms2) _ _ p4 w4 HAR0 Hsp2 AP4 KF
             ltac:(cwa_unf; lia) ltac:(cwa_unf; lia)). }
         assert (HXW : x3 = (if 4 <? r then w4 else S_DASH))
         by (rewrite HX3; exact (proj2 (cwh_client_word r w3 w4 ltac:(lia) HPL))).
         assert (HFRM : cwa_frame (mrestrict (w_H W) (ms_mem ms2)) (spZ regs) regs).
         { pose proof (st_ok_region_nth (segs := SEGS) _ _ _ 1%nat _ HS eq_refl) as HRG.
           cbn [ms_mem restrict] in HRG.
           exact (cwh_frame_all _ W _ (spZ regs) regs HRG Esph ENh). }
         pmkst HS.
         prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
         prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18.
         prreg HS (19%bv : bv 5) P19. prreg HS (21%bv : bv 5) P21.
         assert (T2 : getr (ms_regs ms2) 2 = w64 (spZ regs - 64))
         by (rewrite P2, Esp; unfold w64; f_equal; lia).
         assert (T3 : getr (ms_regs ms2) 3 = getr regs 3)
         by (rewrite P3; exact (EN 3%nat 3%bv ltac:(lia) eq_refl)).
         assert (T4 : getr (ms_regs ms2) 4 = getr regs 4)
         by (rewrite P4; exact (EN 4%nat 4%bv ltac:(lia) eq_refl)).
         assert (T8 : getr (ms_regs ms2) 8 = w64 cp)
         by (rewrite P8, (EN 10%nat 10%bv ltac:(lia) eq_refl); exact R10).
         assert (T9 : getr (ms_regs ms2) 9 = w64 p3) by (rewrite P9, Ea33; reflexivity).
         assert (T18 : getr (ms_regs ms2) 18 = w64 wp)
         by (rewrite P18, (EN 11%nat 11%bv ltac:(lia) eq_refl); exact R11).
         assert (T19 : getr (ms_regs ms2) 19 = w64 r)
         by (rewrite P19, (EN 12%nat 12%bv ltac:(lia) eq_refl); exact R12).
         assert (T21 : getr (ms_regs ms2) 21 = w64 SHADOW_OFF)
         by (rewrite P21, Ea32; reflexivity).
         assert (Thi : forall rr, 22 <= rr <= 27 ->
         getr (ms_regs ms2) (Z_to_bv 5 rr) = getr regs (Z_to_bv 5 rr)).
         { intros rr Hrr.
           assert (Hc' : rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia.
           repeat (destruct Hc' as [-> | Hc']); [..|subst rr];
           lazymatch goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
             let G := fresh "G" in prreg HS (Z_to_bv 5 k) G; rewrite G end;
           lazymatch goal with |- ew _ ?n = getr _ ?r2 =>
             exact (EN n r2 ltac:(lia) eq_refl) end. }
         exact (cwa_mid_word B RLO RHI HFACTS ly S W regs mem md cp q2 q3 wp r p3 p4 x3 w3 w4
         (ms_mem ms2) mdv4 (ms_regs ms2) HPRE HRO HJ3 VOBJS ASTRCMP ROKf T2 T3 T4 Thi T8 T9 T18 T19
         T21 ltac:(lia) HFRM Hcp1 Hcp2 Hcp8 Hwp8 HNf HQ2f HQ3f AQ2f AQ3f AP3f HPL AW4f HXW).
      -- (* word 3 is not "default": the third wrapper call, against the prefix "pool:" *)
         rewrite branch_eq_U, HU84, HU0 in Hc0. apply Z.eqb_neq in Hc0.
         assert (HNDEF : bytes_eqb w3 S_DEFAULT = false).
         { destruct (bytes_eqb w3 S_DEFAULT) eqn:Eq; [|reflexivity]. exfalso.
           apply Hc0. apply cwh_zero_iff. apply (proj2 HQr3). apply bytes_eqb_iff. exact Eq. }
         clear Q1 Q2 Q3 Q4 Q10 Q11 Qsp Qgp Qtp Qra Qa0 Qa1 Hspd HEP ROMd HC
         SP3d RP3d TP3d SDEF RDEF TDEF HBdef K13 K14 KC2.
         paj_run_tok RUN HS HJ3 SHOK2 CWA_SPAN; [awr_ok_tac; exact Esph |].
         lazymatch goal with |- SRr _ _ (mkCfg _ ?mdq) _ =>
           set (mdv4 := mdq) in *; clearbody mdv4 end.
         assert (K5 : kept_out (rdW W mem3) (rdW W (ms_mem ms2)) (spZ regs - 64) (spZ regs)).
         { apply (cwh_mem_kept _ W _ _ _ _ _ HFr).
           intros b wlo whi a Hin Hr'.
           cbv [windows] in Hin. cbn [map In YP09.r_base YP09.r_wlo YP09.r_whi] in Hin.
           repeat (destruct Hin as [Heq | Hin];
                   [inversion Heq; subst; cbn [base_val] in Hr'; rewrite ?Esph in Hr'; lia |]);
           destruct Hin. }
         assert (K5w : kept_out (rdW W mem3) (rdW W (ms_mem ms2))
         (spZ regs - 64 - 2 * ESTACK) (spZ regs)).
         { apply (cwh_kept_wide _ _ (spZ regs - 64) (spZ regs)); [exact K5 | cwa_unf; lia | lia]. }
         assert (K16 : kept_out (rdW W mem) (rdW W (ms_mem ms2))
         (spZ regs - 64 - 2 * ESTACK) (spZ regs))
         by (exact (kept_out_trans _ _ _ _ _ _ _ K15 K5w ltac:(lia) ltac:(lia))).
         clear HF HFr HG K5 K5w.
         assert (ROKp : cmd_ro_ok (rdW W (ms_mem ms2)))
         by (exact (cwh_ro_kept _ _ _ _ K16 ltac:(cwa_unf; lia) ltac:(cwa_unf; lia) HROK)).
         assert (AP3p : cwa_str B ly S (rdW W (ms_mem ms2)) p3 w3)
         by (exact (cwh_argA_kept ly S W regs mem md (ms_mem ms2) _ _ p3 w3 HAR0 Hsp2 AP3 K16
             ltac:(cwa_unf; lia) ltac:(cwa_unf; lia))).
         pmkst HS.
         prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
         prreg HS (4%bv : bv 5) Q4. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
         prreg HS (12%bv : bv 5) Q12.
         assert (Qsp : spZ (ms_regs ms2) = spZ regs + (-64)).
         { unfold spZ in *. rewrite Q2, Esp. apply unsigned_lit_small. cwa_unf; lia. }
         assert (Qgp : getr (ms_regs ms2) 3 = w64 (as_gp B))
         by (rewrite Q3, (EN 3%nat 3%bv ltac:(lia) eq_refl); exact Hgp).
         assert (Qtp : getr (ms_regs ms2) 4 = w64 (as_tp B))
         by (rewrite Q4, (EN 4%nat 4%bv ltac:(lia) eq_refl); exact Htp).
         assert (Qra : YK0s.ret_ok (getr (ms_regs ms2) 1))
         by (rewrite Q1; apply ret_ok_codeptr_v;
             [cbv; split; [congruence | reflexivity] | reflexivity]).
         assert (Qa0 : getr (ms_regs ms2) 10 = w64 p3) by (rewrite Q10, Ea33; reflexivity).
         assert (Ea273 : ew E 273 = Z_to_bv 64 (VAL (A_OBJ 32)))
         by (unfold E, cwa_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
         assert (VO32 : VAL (A_OBJ 32) = 0x21b60)
         by (rewrite (VOBJS 32%nat ltac:(vm_compute; lia)); vm_compute; reflexivity).
         assert (Qa1 : getr (ms_regs ms2) 11 = w64 0x21b60)
         by (rewrite Q11, Ea273, VO32; reflexivity).
         assert (Qa2 : getr (ms_regs ms2) 12 = w64 5) by (rewrite Q12; reflexivity).
         assert (Hspp : alloc_ceiling <= spZ (ms_regs ms2) - 2 * ESTACK)
         by (rewrite Qsp; cwa_unf; lia).
         destruct (cwa_str_facts B ly S W (ms_regs ms2) (ms_mem ms2) mdv4 p3 w3
         (proj1 HJ3) AP3p Hspp) as (_ & SP3p & RP3p & TP3p & _ & _).
         assert (HBpool : abytes_atR (rdW W (ms_mem ms2)) 0x21b60 RO_lit_21b60)
         by (destruct ROKp as [HROB _]; unfold cmd_ro_bytes in HROB;
             repeat (destruct HROB as [? HROB]); assumption).
         destruct (cwh_lit_str ly S W (ms_regs ms2) (ms_mem ms2) mdv4 0x21b60 6 RO_lit_21b60 S_POOL
         (proj1 HJ3) ROKp Hspp ltac:(cbv [CWA_LITS In]; tauto) HBpool
         ltac:(cbv [cmd_ro_ends In]; tauto) ltac:(vm_compute; reflexivity)
         ltac:(apply notin_nul_lit; vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
         as (SPOOL & RPOOL & TPOOL).
         assert (HEP : ecall_pre_stk SEGS B (2 * ESTACK) ly S W (ms_regs ms2) (ms_mem ms2) mdv4).
         { eapply (ecall_pre_stk_at SEGS B
           (2 * ESTACK) CHECK_WORDS_ADD_STK (spZ regs) [] ly S W mem md [] ly S W (ms_mem ms2) _ 0
           (ms_regs ms2) (-64) HJ3 Qsp);
           [reflexivity | lia | unfold ESTACK; lia | unfold CHECK_WORDS_ADD_STK, ESTACK; lia
           | exact Qra | exact Qgp | exact Qtp]. }
         assert (ROMp : rt_rom_view SEGS B W (ms_mem ms2))
         by (eapply (cwa_rom_at B RLO RHI); [exact HRO | exact HJ3]).
         assert (RP3n : aread_ok SEGS (2 * ESTACK) W (ms_regs ms2) (ms_mem ms2) p3
         (Z.min 5 (astr_len w3 + 1))).
         { apply (cwh_read_shrink _ W _ _ _ (astr_len w3 + 1));
           [exact RP3p | unfold astr_len; pose proof (Zle_0_nat (length w3)); lia]. }
         assert (RPOOLn : aread_ok SEGS (2 * ESTACK) W (ms_regs ms2) (ms_mem ms2) 0x21b60
         (Z.min 5 (astr_len S_POOL + 1))).
         { apply (cwh_read_shrink _ W _ _ _ (astr_len S_POOL + 1));
           [exact RPOOL | unfold astr_len; cbn [length S_POOL str map]; lia]. }
         (* the contract's band premises (a Theorem Labs lane's string-band.md section 4, the strncmp at 0x88f58): word 3 is a heap
            string in the harness's `copy` block (H), "pool:" a read-only literal of the image (R) *)
         assert (MP3 : amem_range p3 (astr_len w3 + 8)).
         { destruct AP3p as (_ & HBK3 & _).
           exact (PaLibH.amem8_of_blockA SEGS B (cwa_laws B) ly S W (ms_mem ms2) mdv4 p3 (astr_len w3)
             (proj1 HJ3) HBK3 (Zle_0_nat (length w3))). }
         assert (MPOOL : amem_range 0x21b60 (astr_len S_POOL + 8)).
         { replace (astr_len S_POOL) with 5 by reflexivity.
           apply PaLibH.amem8_of_low; unfold kLowMemEnd; lia. }
         pose proof (ASTRNCMP ly S W (ms_regs ms2) (ms_mem ms2) mdv4 p3 0x21b60 5 w3 S_POOL
         HEP Qa0 Qa1 Qa2 ltac:(lia) ltac:(lia) ltac:(lia) SP3p SPOOL RP3n MP3 RPOOLn MPOOL TP3p TPOOL ROMp)
         as HC.
         eapply SRr_bind.
         { eapply (aj_art_at SEGS B (cwa_laws B) Hsegs (cf_env B HFACTS) (2 * ESTACK)
           (fun _ => False) (SIGMA CS___interceptor_trampoline_strncmp) W (ms_regs ms2)
           (ms_mem ms2) CHECK_WORDS_ADD_STK (spZ regs) [] ly S W mem md [] ly S mdv4 0 (-64)
           (getr (ms_regs ms2) 1) _
           HJ3 Qsp ltac:(reflexivity) ltac:(lia) ltac:(unfold ESTACK; lia)
           ltac:(unfold CHECK_WORDS_ADD_STK, ESTACK; lia)
           eq_refl (fun a H => False_ind _ H) HC). }
         cbv beta. intros W4 c4 _ (HW4 & regs4 & mem4 & md4 & Hc4 & HJ4 & HP4 & HQr4 & HKP4).
         subst W4 c4.
         rewrite Q1.
         pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres4 & _ & _ & _).
         jafter_call_keep_pi HS 108%nat regs4 (mrestrict (w_H W) mem4) HP4 [0; 1; 2; 3]%nat HS4.
         match type of HS4 with ?t -> _ => assert (HRK : t); [|specialize (HS4 HRK); clear HRK] end.
         { cbn [ms_mem restrict].
           repeat apply Forall_cons; try apply Forall_nil;
           cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi].
           - apply (cwa_region_kept _ W (ms_mem ms2) mem4 _
             (spZ regs + -64 - 2 * ESTACK) (spZ regs + -64));
             [ intros a Ha Hn; exact (HKP4 a Ha Hn (fun x => x)) | .. ];
             cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi];
             cbn [ew havoc nth map CLOB Nat.ltb Nat.leb Nat.sub];
             rewrite ?BW; cwa_unf; lia.
           - apply (cwh_region_kept_w _ W (ms_mem ms2) mem4 _
             (spZ regs + -64 - 2 * ESTACK) (spZ regs + -64));
             [ intros a Ha Hn; exact (HKP4 a Ha Hn (fun x => x)) | .. ];
             cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi];
             cbn [ew havoc nth map CLOB Nat.ltb Nat.leb Nat.sub];
             rewrite ?Esp; try (cwa_unf; lia).
             intros a Ha. apply Hpres4. cwa_unf; lia.
           - apply (cwa_region_kept _ W (ms_mem ms2) mem4 _
             (spZ regs + -64 - 2 * ESTACK) (spZ regs + -64));
             [ intros a Ha Hn; exact (HKP4 a Ha Hn (fun x => x)) | .. ];
             cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi];
             cbn [ew havoc nth map CLOB Nat.ltb Nat.leb Nat.sub];
             rewrite ?BG; cwa_unf; lia.
           - apply (cwa_region_kept _ W (ms_mem ms2) mem4 _
             (spZ regs + -64 - 2 * ESTACK) (spZ regs + -64));
             [ intros a Ha Hn; exact (HKP4 a Ha Hn (fun x => x)) | .. ];
             cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi];
             cbn [ew havoc nth map CLOB Nat.ltb Nat.leb Nat.sub];
             rewrite ?BC; cwa_unf; lia. }
         clear HS. rewrite <- restrict_mkst_fx in HS4. rename HS4 into HS.
         clear HEIh ENh Esph Ea33h Ea32h Ea84h HU84 HU0 SHOK2.
         lazymatch type of HS with st_ok_pi _ _ ?Eh _ _ =>
         assert (HEIh : img_env VAL A_LIM Eh) by (apply img_env_havoc; [assumption | cbv; lia]);
         assert (ENh : forall (n : nat) (rr : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned rr ->
         ew Eh n = getr regs rr)
         by (intros n rr Hn Hrr; rewrite !ew_havoc_old by lia; exact (EN n rr Hn Hrr));
         assert (Esph : bv_unsigned (ew Eh 2) = spZ regs)
         by (rewrite !ew_havoc_old by lia; exact Esp);
         assert (Ea33h : ew Eh 33 = Z_to_bv 64 p3)
         by (rewrite !ew_havoc_old by lia; exact Ea33);
         assert (Ea32h : ew Eh 32 = Z_to_bv 64 SHADOW_OFF)
         by (rewrite !ew_havoc_old by lia; exact Ea32);
         assert (Ea270h : ew Eh 270 = Z_to_bv 64 (VAL (A_OBJ 29)))
         by (rewrite !ew_havoc_above by (cbv; lia); exact Ea270);
         assert (Ea112h : ew Eh 112 = getr regs4 10)
         by (cbn [ew havoc nth map CLOB Nat.ltb Nat.leb Nat.sub]; reflexivity);
         assert (SHOK2 : sh_ok SEGS CWA_BX [] Eh (mrestrict (w_H W) mem4)) by constructor;
         assert (HU112 : U Eh (SOff 112 0) = bv_unsigned (getr regs4 10))
         by (unfold U; cbn [sv_denot]; rewrite Ea112h, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity);
         assert (HU0 : U Eh (SLit 0) = 0)
         by (unfold U; cbn [sv_denot]; apply unsigned_lit_small; lia) end.
         assert (KC3 : kept_out (rdW W (ms_mem ms2)) (rdW W mem4)
         (spZ regs - 64 - 2 * ESTACK) (spZ regs))
         by (intros a Ha Hn; exact (HKP4 a Ha ltac:(cwa_unf; lia) (fun x => x))).
         assert (K17 : kept_out (rdW W mem) (rdW W mem4) (spZ regs - 64 - 2 * ESTACK) (spZ regs))
         by (exact (kept_out_trans _ _ _ _ _ _ _ K16 KC3 ltac:(lia) ltac:(lia))).
         (* the third answer, as the model states it *)
         assert (HnulW3 : ~ In (Z_to_bv 8 0) w3) by (exact (proj2 SP3p)).
         destruct (strncmp_prefix w3 S_POOL HnulW3
         ltac:(apply notin_nul_lit; vm_compute; reflexivity) ltac:(vm_compute; discriminate))
         as (vp & HvP & HiffP).
         replace (Z.of_nat (length S_POOL)) with 5 in HvP by (vm_compute; reflexivity).
         unfold NUL in HvP.
         assert (HPOOLiff : getr regs4 10 = w64 0 <-> prefixb w3 S_POOL = true).
         { rewrite HQr4, HvP. split.
           - intros HE. apply prefixb_iff. apply HiffP. injection HE as HE. exact HE.
           - intros HP. f_equal. apply HiffP. apply prefixb_iff. exact HP. }
         psrr_branch_tok RUN BR HS SHOK2 CWA_SPAN.
         ++ (* no match: the placement stays the image literal "-" *)
            rewrite branch_ne_U, HU112, HU0 in Hc1.
            apply negb_true_iff in Hc1. apply Z.eqb_neq in Hc1.
            assert (HNPOOL : prefixb w3 S_POOL = false).
            { apply not_true_is_false. intros HP. apply Hc1. apply cwh_zero_iff.
              apply (proj2 HPOOLiff). exact HP. }
            assert (HNPL : PCwa.is_placement_b w3 = false)
            by (unfold PCwa.is_placement_b; rewrite HNOWN, HNDEF, HNPOOL; reflexivity).
            assert (Hpf : (3 <? r) && PCwa.is_placement_b w3 = false)
            by (rewrite HNPL, andb_false_r; reflexivity).
            paj_run_to_tok RUNTO HS HJ4 SHOK2 CWA_SPAN 0x2a34; [awr_ok_tac; exact Esph |].
            lazymatch goal with |- SRr _ _ (mkCfg _ ?mdq) _ =>
              set (mdv5 := mdq) in *; clearbody mdv5 end.
            assert (K6 : kept_out (rdW W mem4) (rdW W (ms_mem ms3)) (spZ regs - 64) (spZ regs)).
            { apply (cwh_mem_kept _ W _ _ _ _ _ HFr).
              intros b wlo whi a Hin Hr'.
              cbv [windows] in Hin. cbn [map In YP09.r_base YP09.r_wlo YP09.r_whi] in Hin.
              repeat (destruct Hin as [Heq | Hin];
                      [inversion Heq; subst; cbn [base_val] in Hr'; rewrite ?Esph in Hr'; lia |]);
              destruct Hin. }
            assert (K6w : kept_out (rdW W mem4) (rdW W (ms_mem ms3))
            (spZ regs - 64 - 2 * ESTACK) (spZ regs)).
            { apply (cwh_kept_wide _ _ (spZ regs - 64) (spZ regs));
              [exact K6 | cwa_unf; lia | lia]. }
            assert (KF : kept_out (rdW W mem) (rdW W (ms_mem ms3))
            (spZ regs - 64 - 2 * ESTACK) (spZ regs))
            by (exact (kept_out_trans _ _ _ _ _ _ _ K17 K6w ltac:(lia) ltac:(lia))).
            assert (ROKf : cmd_ro_ok (rdW W (ms_mem ms3)))
            by (exact (cwh_ro_kept _ _ _ _ KF ltac:(cwa_unf; lia) ltac:(cwa_unf; lia) HROK)).
            assert (HNf : aval_mem (rdW W (ms_mem ms3)) (cp + CALL_OFF_NARGS) 4 4)
            by (exact (cwh_val_kept W mem (ms_mem ms3) _ _ _ 4%nat 4 KF HN
                ltac:(cwh_unf; lia) ltac:(cwh_unf; lia) ltac:(cwa_unf; lia))).
            assert (HQ2f : aval_mem (rdW W (ms_mem ms3)) (cp + CALL_OFF_ARGS + 16) 8 q2)
            by (exact (cwh_val_kept W mem (ms_mem ms3) _ _ _ 8%nat q2 KF HV2
                ltac:(cwh_unf; lia) ltac:(cwh_unf; lia) ltac:(cwa_unf; lia))).
            assert (HQ3f : aval_mem (rdW W (ms_mem ms3)) (cp + CALL_OFF_ARGS + 24) 8 q3)
            by (exact (cwh_val_kept W mem (ms_mem ms3) _ _ _ 8%nat q3 KF HV3
                ltac:(cwh_unf; lia) ltac:(cwh_unf; lia) ltac:(cwa_unf; lia))).
            assert (HX2D : x2 = S_DASH)
            by (rewrite HX2; unfold PCwa.add_placement; rewrite Hpf; reflexivity).
            assert (AQ2f : cwa_str B ly S (rdW W (ms_mem ms3)) q2 S_DASH).
            { rewrite <- HX2D.
              exact (cwh_argA_kept ly S W regs mem md (ms_mem ms3) _ _ q2 x2 HAR0 Hsp2 AQ2 KF
              ltac:(cwa_unf; lia) ltac:(cwa_unf; lia)). }
            assert (AQ3f : cwa_str B ly S (rdW W (ms_mem ms3)) q3 x3)
            by (exact (cwh_argA_kept ly S W regs mem md (ms_mem ms3) _ _ q3 x3 HAR0 Hsp2 AQ3 KF
                ltac:(cwa_unf; lia) ltac:(cwa_unf; lia))).
            assert (AW3f : 3 < r -> in_blockA (ablocks B ly S) (wp + 24) 8 /\
            aval_mem (rdW W (ms_mem ms3)) (wp + 24) 8 p3 /\
            cwa_str B ly S (rdW W (ms_mem ms3)) p3 w3).
            { intros _. split; [exists qb, kb; auto|]. split.
              - exact (cwh_val_kept W mem (ms_mem ms3) _ _ _ 8%nat p3 KF HVW
                ltac:(cwa_unf; lia) ltac:(cwa_unf; lia) ltac:(cwa_unf; lia)).
              - exact (cwh_argA_kept ly S W regs mem md (ms_mem ms3) _ _ p3 w3 HAR0 Hsp2 AP3 KF
                ltac:(cwa_unf; lia) ltac:(cwa_unf; lia)). }
            assert (HXD : x3 = (if 3 <? r then w3 else S_DASH))
            by (rewrite HX3; exact (cwh_client_dash r w3 w4 Hpf)).
            assert (HFRM : cwa_frame (mrestrict (w_H W) (ms_mem ms3)) (spZ regs) regs).
            { pose proof (st_ok_region_nth (segs := SEGS) _ _ _ 1%nat _ HS eq_refl) as HRG.
              cbn [ms_mem restrict] in HRG.
              exact (cwh_frame_all _ W _ (spZ regs) regs HRG Esph ENh). }
            pmkst HS.
            prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
            prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18.
            prreg HS (19%bv : bv 5) P19. prreg HS (21%bv : bv 5) P21.
            assert (T2 : getr (ms_regs ms3) 2 = w64 (spZ regs - 64))
            by (rewrite P2, Esp; unfold w64; f_equal; lia).
            assert (T3 : getr (ms_regs ms3) 3 = getr regs 3)
            by (rewrite P3; exact (EN 3%nat 3%bv ltac:(lia) eq_refl)).
            assert (T4 : getr (ms_regs ms3) 4 = getr regs 4)
            by (rewrite P4; exact (EN 4%nat 4%bv ltac:(lia) eq_refl)).
            assert (T8 : getr (ms_regs ms3) 8 = w64 cp)
            by (rewrite P8, (EN 10%nat 10%bv ltac:(lia) eq_refl); exact R10).
            assert (T9 : getr (ms_regs ms3) 9 = w64 0x21b00)
            by (rewrite P9, Ea270, VO29; reflexivity).
            assert (T18 : getr (ms_regs ms3) 18 = w64 wp)
            by (rewrite P18, (EN 11%nat 11%bv ltac:(lia) eq_refl); exact R11).
            assert (T19 : getr (ms_regs ms3) 19 = w64 r)
            by (rewrite P19, (EN 12%nat 12%bv ltac:(lia) eq_refl); exact R12).
            assert (T21 : getr (ms_regs ms3) 21 = w64 SHADOW_OFF)
            by (rewrite P21, Ea32; reflexivity).
            assert (Thi : forall rr, 22 <= rr <= 27 ->
            getr (ms_regs ms3) (Z_to_bv 5 rr) = getr regs (Z_to_bv 5 rr)).
            { intros rr Hrr.
              assert (Hc' : rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia.
              repeat (destruct Hc' as [-> | Hc']); [..|subst rr];
              lazymatch goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
                let G := fresh "G" in prreg HS (Z_to_bv 5 k) G; rewrite G end;
              lazymatch goal with |- ew _ ?n = getr _ ?r2 =>
                exact (EN n r2 ltac:(lia) eq_refl) end. }
            exact (cwa_mid_dash B RLO RHI HFACTS ly S W regs mem md cp q2 q3 wp r p3 x3 w3
            (ms_mem ms3) mdv5 (ms_regs ms3) HPRE HRO HJ4 VOBJS ASTRCMP ROKf T2 T3 T4 Thi T8 T9
            T18 T19 T21 Hr HFRM Hcp1 Hcp2 Hcp8 Hwp8 HNf HQ2f HQ3f AQ2f AQ3f AW3f HXD).
         ++ (* word 3 has the prefix "pool:": the placement is word 3 *)
            rewrite branch_ne_U, HU112, HU0 in Hc1.
            apply negb_false_iff in Hc1. apply Z.eqb_eq in Hc1.
            assert (HPOOLt : prefixb w3 S_POOL = true)
            by (apply (proj1 HPOOLiff); apply cwh_zero_iff; exact Hc1).
            assert (HPL : PCwa.is_placement_b w3 = true)
            by (unfold PCwa.is_placement_b; rewrite HPOOLt, orb_true_r; reflexivity).
            paj_run_to_tok RUNTO HS HJ4 SHOK2 CWA_SPAN 0x2a34; [awr_ok_tac; exact Esph |].
            lazymatch goal with |- SRr _ _ (mkCfg _ ?mdq) _ =>
              set (mdv5 := mdq) in *; clearbody mdv5 end.
            assert (K6 : kept_out (rdW W mem4) (rdW W (ms_mem ms3)) (spZ regs - 64) (spZ regs)).
            { apply (cwh_mem_kept _ W _ _ _ _ _ HFr).
              intros b wlo whi a Hin Hr'.
              cbv [windows] in Hin. cbn [map In YP09.r_base YP09.r_wlo YP09.r_whi] in Hin.
              repeat (destruct Hin as [Heq | Hin];
                      [inversion Heq; subst; cbn [base_val] in Hr'; rewrite ?Esph in Hr'; lia |]);
              destruct Hin. }
            assert (K6w : kept_out (rdW W mem4) (rdW W (ms_mem ms3))
            (spZ regs - 64 - 2 * ESTACK) (spZ regs)).
            { apply (cwh_kept_wide _ _ (spZ regs - 64) (spZ regs));
              [exact K6 | cwa_unf; lia | lia]. }
            assert (KF : kept_out (rdW W mem) (rdW W (ms_mem ms3))
            (spZ regs - 64 - 2 * ESTACK) (spZ regs))
            by (exact (kept_out_trans _ _ _ _ _ _ _ K17 K6w ltac:(lia) ltac:(lia))).
            assert (ROKf : cmd_ro_ok (rdW W (ms_mem ms3)))
            by (exact (cwh_ro_kept _ _ _ _ KF ltac:(cwa_unf; lia) ltac:(cwa_unf; lia) HROK)).
            assert (HNf : aval_mem (rdW W (ms_mem ms3)) (cp + CALL_OFF_NARGS) 4 4)
            by (exact (cwh_val_kept W mem (ms_mem ms3) _ _ _ 4%nat 4 KF HN
                ltac:(cwh_unf; lia) ltac:(cwh_unf; lia) ltac:(cwa_unf; lia))).
            assert (HQ2f : aval_mem (rdW W (ms_mem ms3)) (cp + CALL_OFF_ARGS + 16) 8 q2)
            by (exact (cwh_val_kept W mem (ms_mem ms3) _ _ _ 8%nat q2 KF HV2
                ltac:(cwh_unf; lia) ltac:(cwh_unf; lia) ltac:(cwa_unf; lia))).
            assert (HQ3f : aval_mem (rdW W (ms_mem ms3)) (cp + CALL_OFF_ARGS + 24) 8 q3)
            by (exact (cwh_val_kept W mem (ms_mem ms3) _ _ _ 8%nat q3 KF HV3
                ltac:(cwh_unf; lia) ltac:(cwh_unf; lia) ltac:(cwa_unf; lia))).
            assert (HX2W : x2 = w3)
            by (rewrite HX2; exact (proj1 (cwh_client_word r w3 w4 ltac:(lia) HPL))).
            assert (AQ2f : cwa_str B ly S (rdW W (ms_mem ms3)) q2 w3).
            { rewrite <- HX2W.
              exact (cwh_argA_kept ly S W regs mem md (ms_mem ms3) _ _ q2 x2 HAR0 Hsp2 AQ2 KF
              ltac:(cwa_unf; lia) ltac:(cwa_unf; lia)). }
            assert (AQ3f : cwa_str B ly S (rdW W (ms_mem ms3)) q3 x3)
            by (exact (cwh_argA_kept ly S W regs mem md (ms_mem ms3) _ _ q3 x3 HAR0 Hsp2 AQ3 KF
                ltac:(cwa_unf; lia) ltac:(cwa_unf; lia))).
            assert (AP3f : cwa_str B ly S (rdW W (ms_mem ms3)) p3 w3)
            by (exact (cwh_argA_kept ly S W regs mem md (ms_mem ms3) _ _ p3 w3 HAR0 Hsp2 AP3 KF
                ltac:(cwa_unf; lia) ltac:(cwa_unf; lia))).
            assert (AW4f : 4 < r -> in_blockA (ablocks B ly S) (wp + 32) 8 /\
            aval_mem (rdW W (ms_mem ms3)) (wp + 32) 8 p4 /\
            cwa_str B ly S (rdW W (ms_mem ms3)) p4 w4).
            { intros H4. destruct (AW4 H4) as (HB4 & HV4 & AP4).
              pose proof HB4 as (qc & kc & Hinc & Hqc1 & Hqc2).
              destruct (al_blocks _ _ (cwa_laws B) _ _ _ _ _ qc kc HAR0 Hinc)
              as (_ & Hc4096 & Hcceil & _ & _ & _).
              pose proof (req_size_pos kc ltac:(lia)) as [Hkc1 Hkc2].
              split; [exact HB4|]. split.
              - exact (cwh_val_kept W mem (ms_mem ms3) _ _ _ 8%nat p4 KF HV4
                ltac:(cwa_unf; lia) ltac:(cwa_unf; lia) ltac:(cwa_unf; lia)).
              - exact (cwh_argA_kept ly S W regs mem md (ms_mem ms3) _ _ p4 w4 HAR0 Hsp2 AP4 KF
                ltac:(cwa_unf; lia) ltac:(cwa_unf; lia)). }
            assert (HXW : x3 = (if 4 <? r then w4 else S_DASH))
            by (rewrite HX3; exact (proj2 (cwh_client_word r w3 w4 ltac:(lia) HPL))).
            assert (HFRM : cwa_frame (mrestrict (w_H W) (ms_mem ms3)) (spZ regs) regs).
            { pose proof (st_ok_region_nth (segs := SEGS) _ _ _ 1%nat _ HS eq_refl) as HRG.
              cbn [ms_mem restrict] in HRG.
              exact (cwh_frame_all _ W _ (spZ regs) regs HRG Esph ENh). }
            pmkst HS.
            prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
            prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18.
            prreg HS (19%bv : bv 5) P19. prreg HS (21%bv : bv 5) P21.
            assert (T2 : getr (ms_regs ms3) 2 = w64 (spZ regs - 64))
            by (rewrite P2, Esp; unfold w64; f_equal; lia).
            assert (T3 : getr (ms_regs ms3) 3 = getr regs 3)
            by (rewrite P3; exact (EN 3%nat 3%bv ltac:(lia) eq_refl)).
            assert (T4 : getr (ms_regs ms3) 4 = getr regs 4)
            by (rewrite P4; exact (EN 4%nat 4%bv ltac:(lia) eq_refl)).
            assert (T8 : getr (ms_regs ms3) 8 = w64 cp)
            by (rewrite P8, (EN 10%nat 10%bv ltac:(lia) eq_refl); exact R10).
            assert (T9 : getr (ms_regs ms3) 9 = w64 p3) by (rewrite P9, Ea33; reflexivity).
            assert (T18 : getr (ms_regs ms3) 18 = w64 wp)
            by (rewrite P18, (EN 11%nat 11%bv ltac:(lia) eq_refl); exact R11).
            assert (T19 : getr (ms_regs ms3) 19 = w64 r)
            by (rewrite P19, (EN 12%nat 12%bv ltac:(lia) eq_refl); exact R12).
            assert (T21 : getr (ms_regs ms3) 21 = w64 SHADOW_OFF)
            by (rewrite P21, Ea32; reflexivity).
            assert (Thi : forall rr, 22 <= rr <= 27 ->
            getr (ms_regs ms3) (Z_to_bv 5 rr) = getr regs (Z_to_bv 5 rr)).
            { intros rr Hrr.
              assert (Hc' : rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia.
              repeat (destruct Hc' as [-> | Hc']); [..|subst rr];
              lazymatch goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
                let G := fresh "G" in prreg HS (Z_to_bv 5 k) G; rewrite G end;
              lazymatch goal with |- ew _ ?n = getr _ ?r2 =>
                exact (EN n r2 ltac:(lia) eq_refl) end. }
            exact (cwa_mid_word B RLO RHI HFACTS ly S W regs mem md cp q2 q3 wp r p3 p4 x3 w3 w4
            (ms_mem ms3) mdv5 (ms_regs ms3) HPRE HRO HJ4 VOBJS ASTRCMP ROKf T2 T3 T4 Thi T8 T9 T18
            T19 T21 ltac:(lia) HFRM Hcp1 Hcp2 Hcp8 Hwp8 HNf HQ2f HQ3f AQ2f AQ3f AP3f HPL AW4f HXW).
  + unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem restrict mkst].
    cbn [base_val]. rewrite BW.
    split; [cwa_unf; lia|]. split; [cwa_unf; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ wp 24 8 (SOff 33 0) p3);
    [ cbn [sv_denot]; rewrite Ea33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | cbn; lia | cbn; lia |].
    exact (cwa_val_mem W (ms_mem ms) (wp + 24) 8%nat p3 HVWc).
  + cbn [add_atom add_cond ss_mem all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite BW, BG, BC.
    repeat split; cwa_unf; lia.
Qed.

End e.
End f.
End d.
