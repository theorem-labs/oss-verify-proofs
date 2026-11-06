(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/B's walk of pcap_source_open in the asan-ubsan instance of fuzz_pcap
   (libreac v1.9.0; pin fuzz_pcap.asan-ubsan, sha256 9e66f771f22a...; function at 0x811e0 =
   BASE + AF_pcap_source_open, AF = 0xa58), proving lib/A's image-generic contract tpcap_source_open_specX
   (lib/A/Prog/PcapSourceOpenDefs.v) at SEGS = pa_segs, rlo / rhi = pa_relro_lo / pa_relro_hi,
   apath / alen / afile = VAL (A_OBJ 3) / VAL (A_OBJ 4) / VAL (A_OBJ 2) (0x20d00 "<fuzz-input>", g_file_len
   0x5d3e40, g_file 0x5d3e60), with FM_RA and roimg as parameters. At ossv/recipes 25e3d17bdb50 (2026-10-29), there was no released proof of this function at
   this image (rule 24 lookup, a Theorem Labs lane, 22:35Z): the v1.8 ubsan proof (lib/U/Prog/pcap_source_open.v at
   origin/ossv/recipes c8557374ad2e) serves only as the template for the UBSan guards.

   The code. Up to the fopen call it is lib/A's ASan code byte for byte at
   other pcs (asan 0x8145c.. = asan-ubsan 0x811e0..): the prologue saves ra, s0 .. s9 (0x811e0..0x81210) and
   realigns s1 = sp = (sp - 96) & -32 (0x81218); the use-after-return flag is read through the GOT (0x81228
   auipc / 0x8122c ld, listing object 0 = 0x99750) from the runtime cell at 0x81234 (object 16 = 0xa17c0): the
   walk takes it as 1 (the kit's AR_const_law through al_const, with uar_cell_regionP (A_OBJ 16) holding SLit 1;
   the pin's file holds 0 and the runtime sets 1 at init), so 0x81240 `beqz a2` is not taken;
   __asan_stack_malloc_1(0x60) at 0x81248 returns the class-1 frame F (aj_stack_malloc_atS, YC85.v:292), whose
   two caller premises are discharged at op_to_call's frame request: count_cid 1 (frames Sc) < fs_frames 1 from
   op_pre's length (frames Sc) <= 7 through count_cid_le_length and 8 <= fs_frames 1, and the apath premise by
   op_SMP (stack_malloc_progressP from lib/Reusable/YG05.v:70, as cgif_file_fuzzer lib/A/ACed.v:129-130), so
   F >= 4096, 0x8125c `bnez s2` is taken and the machine-frame arm 0x81260..0x81278 is dead; then *(s1) = F
   (0x8127c), the header (0x41b58ab3, objects 10 and 11; 0x812a4..0x812ac), the twelve shadow bytes
   (0x812b8..0x812e4: 0xf1 x4, 0xf8 x3, 0xf3 x5), the mode literal "rb" (object 12, 0x812e8 / 0x812ec; HMODE)
   and the call of libreac_fuzz_fopen (0x812f4) through cl_callS (YC85.v:383) with FOPEN as the callee.

   The cut. This file walks the head: entry -> op_to_call (a Qed checkpoint at the call, op_at_call) ->
   head_to_fopen, which makes the call and establishes PcapSourceOpenPhF.v's op_fopen_ret at the return
   0x812f8. From there PcapSourceOpenPhM.v (op_from_fopen) walks to the two cuts of PcapSourceOpenPh.v and
   PcapSourceOpenB.v (op_from_null / op_from_read) to the return; pb_pcap_source_openX composes the three.
   The three UBSan guards are therefore decided outside this file, at these pcs and against these template lines:
   in PcapSourceOpenPhM.v 0x812f8 `beqz s3` (ps = 0, not taken: ps >= 4096 from op_pre's frame bounds; template
   :114 / :334, premise :93 / :290) and 0x81300 / 0x81304 `andi a0,s3,7; bnez a0` (ps mod 8 <> 0, not taken:
   op_pre's ps mod 8 = 0; template :115 / :335); in PcapSourceOpenB.v 0x81390 / 0x81394 `addi a0,zero,-3;
   bgeu s4,a0` (F + 32 >=u 2^64 - 3, not taken: F + 128 <= alloc_ceiling < 2^47; template :408-412, premise
   :291 and :295-299); all three
   go to the `unimp` at 0x8153c, and every ASan report path 0x81540..0x815b4 is dead because ps's 24 bytes are
   addressable and ps mod 8 = 0. In the head, op_at_call carries what those walks need: ps unwritten and still
   range_addressable, and op_fopen_ret's FILE-block footprint fact for the fclose of the tail.

   The callee hypotheses, used at this image as Section hypotheses: FOPEN : tlibreac_fuzz_fopen_specX
   (lib/A/Prog/PcapFuzzFopenDefs.v), AFREAD : afread_spec (lib/A/Stdio/PFreadISpec.v:138), AFCLOSE :
   afclose_source_spec (lib/A/Stdio/PFclose.v:209), ASM1 : astack_malloc_realizes (lib/Reusable/YG0d.v:285),
   ASF : astack_free_law (lib/Reusable/YG0d.v:301) and FFL : frame_flag_lawP (lib/Reusable/YCbq.v:797), the meter laws MLAW / MLAWF /
   FM, ASIL : asource_img_laws, and the kit's LAWS / TL / TLF / ML. Four instance obligations beyond the kit:
   ROK (roimg reads only image bytes outside the runtime's statics, errno and the open-file list head; applied at
   the fopen call to carry roimg from the entry memory across the prologue and the frame setup), HPATH (the path
   literal's shadow, as a law of every AR state: the frame request's kept clauses do not keep a global's shadow,
   YG0n.v:241 makes it aowned; discharged by the instance through AR_zshadow_law, YG0d.v:435-438), HGX (g_file_len
   and g_file are image bytes outside the runtime's statics and errno; the gx_ok shape of
   lib/A/Prog/PcapEntryDefs.v:366, 395, discharged by the harness), and RO : ro_below_ofl (as
   lib/A/Prog/PcapHarnessTail.v:37). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0s YI16 YG0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05 PcapImgEnd YE00 YG0p YC5d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YG05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym PaShadow.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaRun.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSyms PcapList PcapAddr PcapPa PcapPaLib.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapBase YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import YC1g YC1h YC85 PcapFrame.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import
PSource PSourceMeta PSourceMeter PFmemopenISpec PFreadISpec PFclose.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapFuzzFopenDefs PcapSourceOpenDefs.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSourceOpenPh PcapSourceOpenPhF.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSourceOpenPhM PcapSourceOpenB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* The kit's headers (lib/A/Prog/YC4b.v:23) turn lia's euclidean-division preprocessing off, so every / and mod
   fact below is supplied by hand (div8_eq64, shadow_rng_in, HF8eq) instead of switching the flag back on: with
   the flag on this file's symbolic runs take twenty minutes more (measured, 2026-10-29 00:40Z). *)

(* No global sink_head instance is in scope (a Theorem Labs lane ruling 21:57Z): every journal below uses the Section's SK. *)
Fail Definition sink_head_probe_walk : YI16.sink_head := _.

(* ---- the symbolic state at the entry -------------------------------------- *)
Definition SB_OP : Z := 0x7fff8000.
Definition OBx : sv := SOff 32 0.
Definition OPspan : Z * Z := (SB_OP, SB_OP + 2 ^ 44 - 1).
(* The machine frame below sp: 96 bytes and up to 16 more by the realignment (0x811e0, 0x81218). *)
Definition op_stack : YP09.region := stack_region OPEN_SPAN.
(* The caller's struct, 24 bytes at a0: read-only in this walk (the middle walk, PcapSourceOpenPhM.v, writes it),
   so every run of this walk keeps its bytes and its shadow outside its write windows. *)
Definition op_ps_region : YP09.region := YP09.mkRegion (Some 10%nat) 0 24 0 0 [].
Definition op_regions : smem :=
  [op_stack; got_regionP; bcell_regionP 32; uar_got_regionP (A_OBJ 16); uar_cell_regionP (A_OBJ 16); op_ps_region].
Definition op_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 140737479966720 3); (32%nat, mkAF SB_OP SB_OP 0)] [] [].
Definition ss_op : sstate := mkSS AF_pcap_source_open sr_atoms op_regions None op_facts.
Definition op_SH : list shent := [mkSHE 10 0 24].
Definition op_extra : list word := map (Z_to_bv 64) [SB_OP].

Lemma sp1_facts : forall x, 0 <= x -> x mod 16 = 0 ->
  x - 16 <= 32 * (x / 32) <= x /\ (32 * (x / 32)) mod 32 = 0 /\ (32 * (x / 32)) mod 16 = 0.
Proof.
intros x Hx H16. pose proof (Z.div_mod x 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as M.
pose proof (Z.div_mod x 16 ltac:(lia)) as D16.
assert (x mod 32 = 0 \/ x mod 32 = 16) by lia.
split; [lia|]. split; [rewrite Z.mul_comm; apply Z_mod_mult|].
replace (32 * (x / 32)) with ((2 * (x / 32)) * 16) by lia. apply Z_mod_mult.
Qed.

Lemma land_m32 : forall x, 0 <= x < 2 ^ 64 -> Z.land x (2 ^ 64 - 32) = 32 * (x / 32).
Proof.
intros x Hx.
assert (E1 : 2 ^ 64 - 32 = Z.ldiff (Z.ones 64) (Z.ones 5)) by reflexivity. rewrite E1.
rewrite Z.ldiff_land, Z.land_assoc, <- Z.ldiff_land.
rewrite Z.land_ones, Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32. lia.
Qed.

(* cgif_file_fuzzer lib/A/ACer.v:156-164 (origin/ossv/recipes c8557374ad2e). *)
Lemma denot_and_m32 : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SAlu ALU_AND (SOff n c) (SLit (-32))) = Z_to_bv 64 (32 * ((v + c) / 32)).
Proof.
intros E n v c Hn H0 H1 Hv. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom_off E n v c Hn) by lia.
change (zcanon (-32)) with (2 ^ 64 - 32). rewrite land_m32 by lia. apply zcanon_id. rewrite M64_val.
split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
pose proof (Z.mul_div_le (v + c) 32 ltac:(lia)). lia.
Qed.
Lemma denot_and_m32_add0 : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_AND (SOff n c) (SLit (-32))) (SLit 0)) = Z_to_bv 64 (32 * ((v + c) / 32)).
Proof.
intros E n v c Hn H0 H1 Hv. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (zcanon 0) with 0. rewrite Z.add_0_r.
pose proof (Z.mul_div_le (v + c) 32 ltac:(lia)) as Hle. pose proof (Z.div_pos (v + c) 32 ltac:(lia) ltac:(lia)) as Hp.
assert (HU : U E (SAlu ALU_AND (SOff n c) (SLit (-32))) = 32 * ((v + c) / 32)).
{ unfold U. rewrite (denot_and_m32 E n v c Hn H0 H1 Hv). apply unsigned_lit_small. lia. }
rewrite HU. apply zcanon_id. rewrite M64_val. lia.
Qed.

(* A register's symbolic value, not normalized (prreg normalizes it). *)
Ltac prreg_raw HS r Hr :=
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

(* A 64-aligned address and its shadow: the 8-byte granule arithmetic the frame facts need, done by hand because
   this unit turns lia's euclidean-division preprocessing off (YC4b.v:23). *)
Lemma div8_eq64 : forall a, a mod 64 = 0 -> a = 8 * (a / 8).
Proof.
intros a Ha. pose proof (Z_div_mod_eq_full a 64) as D. rewrite Ha, Z.add_0_r in D.
rewrite D at 2. replace (64 * (a / 64)) with ((8 * (a / 64)) * 8) by lia. rewrite Z.div_mul by lia. lia.
Qed.
Lemma shadow_rng_in : forall fa fb x, fa = 8 * (fa / 8) -> fb = 8 * (fb / 8) -> fa <= x < fa + fb ->
  fa / 8 <= x / 8 < fa / 8 + fb / 8.
Proof.
intros fa fb x Ha Hb Hx. split.
- apply Z.div_le_mono; lia.
- apply Z.div_lt_upper_bound; lia.
Qed.
Lemma ra_frame : forall (rd rd' : Z -> option Z) a n,
  range_addressable rd SHADOW_OFF a n ->
  (forall x, a <= x < a + n -> rd' (shadow_of_addr SHADOW_OFF x) = rd (shadow_of_addr SHADOW_OFF x)) ->
  range_addressable rd' SHADOW_OFF a n.
Proof.
intros rd rd' a n HR Hk x Hx. destruct (HR x Hx) as (s & Hs & Ho). exists s. rewrite Hk by exact Hx.
split; [exact Hs | exact Ho].
Qed.

(* Region trimming (cgif_file_fuzzer lib/A/ACer.v:24-25, 86-91, 131-139). *)
Definition chunk_in (lo hi : Z) (c : YP09.chunk) : bool :=
  Z.leb lo (YP09.c_off c) && Z.leb (YP09.c_off c + YP09.c_len c) hi.
Definition trim_region (r : YP09.region) (lo hi : Z) : YP09.region :=
  YP09.mkRegion (YP09.r_base r) lo hi (Z.max (YP09.r_wlo r) lo) (Z.min (YP09.r_whi r) hi)
    (filter (chunk_in lo hi) (YP09.r_chunks r)).
Fixpoint trim_stack (rs : smem) (lo hi : Z) : smem :=
  match rs with
  | [] => []
  | r :: t => match YP09.r_base r with
              | Some 2%nat => trim_region r lo hi :: t
              | _ => r :: trim_stack t lo hi end end.
Ltac subregion_tac :=
  unfold subregion; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
  split; [reflexivity|]; split; [lia|]; split; [lia|]; split; [lia|];
  let c := fresh "c" in let Hc := fresh "Hc" in intros c Hc; cbn in Hc |- *;
  first [exact Hc | solve [destruct Hc] | tauto].
Ltac submem_to := repeat (first [apply submem_keep; [subregion_tac|] | apply submem_drop]); apply submem_nil.
Ltac norm_pi HS := lazymatch type of HS with st_ok_pi ?a ?b ?c ?ss ?d => let v := eval vm_compute in ss in change ss with v in HS end.
Ltac add_fact HS n f prf :=
  lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
    let HS3 := fresh "HS3" in
    pose proof (st_ok_pi_add_fact Ev ssx msx n f HS ltac:(prf)) as HS3; clear HS; rename HS3 into HS; norm_pi HS end.
(* A region's window closed: the region stays readable but is read-only, so the token engine's cells_safe_b
   (YCbn.v:115-119) accepts a state whose shadow region lies in the band (cgif lib/A/ACbf.v:155-163 fs_ro). *)
Ltac set_ro HS i :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
    let r := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
    let HS3 := fresh "HS3" in
    pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 0) HS ltac:(vm_compute; reflexivity) eq_refl
      ltac:(vm_compute; reflexivity)
      (region_ok_rewindow _ Ex _ r 0 0 (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity))
        ltac:(intros o Ho; lia))) as HS3;
    clear HS; rename HS3 into HS; norm_pi HS end.

(* Drops the hypotheses whose types carry a whole symbolic state or region list. Arithmetic sub-proofs start with it:
   `lia` and `unfold ... in *` traverse every hypothesis, and with the walk's symbolic state in context one
   transport assert took 724 s (measured 2026-10-29 04:59Z build, `Time`), against well under a second without. *)
Ltac clear_big := repeat match goal with
  | H : st_ok_pi _ _ _ _ _ |- _ => clear H
  | H : st_ok _ _ _ _ |- _ => clear H
  | H : frame_of _ _ _ _ |- _ => clear H
  | H : sh_ok _ _ _ _ _ |- _ => clear H
  | H : mem_grows _ _ |- _ => clear H
  end.
(* lia's preprocessing case-splits on every disjunctive hypothesis, so the walk's dozen range facts
   (in_app, off_img, the frame separations) make one side condition cost minutes: 598 s for one transport
   (measured 2026-10-29 05:52Z). Each arithmetic side condition below destructs the disjunctions it needs
   and then drops the rest. *)
Ltac drop_disj := repeat match goal with H : _ \/ _ |- _ => clear H end.
(* Deciding whether the FILE block the call allocated was already a block of the caller's start state:
   the walk's footprint obligation splits on it. *)
Definition zz_eq_dec : forall x y : Z * Z, {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Defined.
Ltac alia := clear_big; drop_disj; lia.
(* A negated range ~(lo <= a < hi) is a disjunction to lia as well: eight of them in one context made one
   side condition run for hours (measured 2026-10-29 12:16-14:40Z). nlia also drops every negation, every
   nested disjunction and every implication; a goal that needs one destructs or applies it first. *)
Ltac drop_neg := repeat match goal with
  | H : ~ _ |- _ => clear H
  | H : _ /\ (_ \/ _) |- _ => clear H
  | H : _ /\ (_ /\ (_ \/ _)) |- _ => clear H
  | H : forall _ : _, _ |- _ => clear H
  end.
Ltac nlia := clear_big; drop_disj; drop_neg; lia.
(* The write rights of a run: the machine-frame window (the caller's journal window covers it) and the regions
   based at a register atom whose bytes lie in a frame of `own` (ps, then this call's own frame). *)
Ltac op_awr spv sp0v Usp :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx own) end;
  repeat first
  [ apply awr_ok_nil
  | eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spv - sp0v);
    [reflexivity | rewrite Usp; lia | cbn [YP09.r_wlo]; unfold OPEN_SPAN, TPCAP_SOURCE_OPEN_STK in *; lia
    | cbn [YP09.r_whi]; lia |]
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
  | eapply awr_ok_cons_gen; [reflexivity | eassumption | cbn [YP09.r_wlo YP09.r_whi]; intros ?a ?Ha |] ].

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg pcap_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ pcap_listing PI).
#[local] Abbreviation VAL := (@pa_val _ pcap_listing PI).
#[local] Abbreviation SIGMA := (@pa_sigma _ pcap_listing PI).
#[local] Abbreviation BASE := (@pa_val _ pcap_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* ---- what a byte-wise memory equality carries (lib/B/Prog/PcapSourceClose.v:86-109) ---- *)
Lemma vm_frame : forall (m m' : word -> option byte) a n v,
  (forall x, a <= x < a + Z.of_nat n -> mbyte SEGS m' x = mbyte SEGS m x) ->
  val_mem SEGS m a n v -> val_mem SEGS m' a n v.
Proof. intros m m' a n v Hfr Hv k Hk. rewrite Hfr by lia. exact (Hv k Hk). Qed.

Lemma asource_none_frame : forall K (m m' : word -> option byte),
  (forall a, asrc_env_addr K a -> mbyte SEGS m' a = mbyte SEGS m a) ->
  asource_none SEGS K m -> asource_none SEGS K m'.
Proof.
intros K m m' Hfr ((Hth & Hnl & Hlk & Hmode & Hms & (cv & Hcv & Hc)) & Hhead).
unfold asource_none, asrc_stdio_env, as_ofl_head in *.
split; [split; [|split; [|split; [|split; [|split]]]]|].
- eapply vm_frame; [|exact Hth]. intros x Hx. apply Hfr. unfold asrc_env_addr. cbn in Hx. lia.
- eapply vm_frame; [|exact Hnl]. intros x Hx. apply Hfr. unfold asrc_env_addr. cbn in Hx. lia.
- eapply vm_frame; [|exact Hlk]. intros x Hx. apply Hfr. unfold asrc_env_addr. cbn in Hx. lia.
- apply (garr8_frame SEGS m m' _ _ Hmode). intros x Hx. apply Hfr. unfold asrc_env_addr.
  cbn [length src_mode_Z app] in Hx. cbn in Hx. lia.
- apply (garr8_frame SEGS m m' _ _ Hms). intros x Hx. apply Hfr. unfold asrc_env_addr.
  cbn [length src_modeset_Z app] in Hx. cbn in Hx. lia.
- exists cv. split; [exact Hcv|]. eapply vm_frame; [|exact Hc]. intros x Hx. apply Hfr.
  unfold asrc_env_addr. cbn in Hx. lia.
- eapply vm_frame; [|exact Hhead]. intros x Hx. apply Hfr. unfold asrc_env_addr. cbn in Hx. lia.
Qed.

(* st_ok's region list, by index (YI3m.v:281's statement at this image's segments). *)
Lemma st_ok_region_nth_g : forall E ss ms i r,
  st_ok SEGS E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok SEGS E (ms_mem ms) r.
Proof.
intros E ss ms i r HS Hi. destruct (st_ok_mem_ok SEGS E ss ms HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.


(* ---- the entry state: what the walk needs of B, its laws and the listing's two runtime cells ---- *)
Section c.
Variable B : asyms.
(* __asan_stack_malloc_1's progress: the allocator's own lemma (cgif_file_fuzzer lib/A/ACed.v:129-130). *)
Lemma op_SMP : stack_malloc_progressP B.
Proof. intros s cid Hc Hn. exact (YG05.stack_malloc_progress (as_universe B) s cid Hc Hn). Qed.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.

Lemma shent_op_ok : forall Ex (m : word -> option byte) ps,
  U Ex OBx = SHADOW_OFF -> U Ex (SOff 10 0) = ps ->
  (4096 <= ps /\ (ps + 24 <= kLowShadowBeg \/ kHighMemBeg <= ps)) ->
  range_addressable (YCbn.rd_of SEGS m) SHADOW_OFF ps 24 ->
  sh_ok SEGS OBx op_SH Ex m.
Proof.
intros Ex m ps HB Hq Hz HR. unfold sh_ok, op_SH. apply Forall_cons; [|apply Forall_nil].
unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HB, Hq. split.
- rewrite Z.add_0_r. exact HR.
- intros a Ha. cbn in Ha. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.

Lemma op_entry : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) ps cid pos,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  getr regs 10 = w64 ps ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - TPCAP_SOURCE_OPEN_STK -> spZ regs <= sp0 ->
  In (cid, pos) own -> In (cid, pos) (frames Sc) ->
  frame_addr lyc cid pos <= ps -> ps + 24 <= frame_addr lyc cid pos + fs_frame_bytes cid -> ps mod 8 = 0 ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF ps 24 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs op_extra)) ss_op
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_pcap_source_open)) memc (seg_rom SEGS))) /\
  sh_ok SEGS OBx op_SH (Eimg (Ereg regs op_extra)) (mrestrict (w_H W) memc).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ps cid pos
  HJ H10 Hal16 Hwlo Hwhi Hown Hin Hfa1 Hfa2 Hps8 Hsh.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (HTS : TPCAP_SOURCE_OPEN_STK = 18736) by reflexivity.
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hf4096 & Hfceil & Hfapp).
pose proof (frm_off_imgP B lyc Sc W memc mdc cid pos HAR Hin) as Hfimg.
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
rewrite (pal_got_uar B TL), (pal_uar_cell B TL) in Kguar. rewrite (pal_uar_cell B TL) in Kuar.
pose proof (pa_obj_img 15 ltac:(lia)) as HcellR. pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
pose proof (pa_obj_img 0 ltac:(lia)) as HguarR. pose proof (pa_obj_img 16 ltac:(lia)) as HuarR.
pose proof (palf_sep B TLF) as Hsep. rewrite (pal_uar_cell B TL) in Hsep. cbn [zseps zseps_from fst snd] in Hsep.
assert (HIE : pcap_img_end = (symaddr ImgPages.AsanUbsan.top)) by reflexivity.
set (E := Eimg (Ereg regs op_extra)).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs op_extra) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 ps) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SB_OP) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (EIMG : forall i, (i < 17)%nat -> ew E (A_OBJ i) = Z_to_bv 64 (VAL (A_OBJ i)))
  by (intros i Hi; subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (U10 : bv_unsigned (ew E 10) = ps) by (rewrite E10; apply unsigned_lit_small; unfold in_app in Hfapp; lia).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (VBI : forall i, (i < 17)%nat -> base_val E (Some (A_OBJ i)) = VAL (A_OBJ i)).
{ intros i Hi. apply VB; [exact (EIMG i Hi) | pose proof (pa_val_range (A_OBJ i)); lia]. }
assert (HPS : forall a, ps <= a < ps + 24 -> apresent (w_H W) memc a).
{ intros a Ha. refine (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ _)).
  right. right. right. exists cid, pos. split; [exact Hown|]. left. unfold in_zr. cbn [fst snd]. lia. }
split.
- rewrite restrict_mkst_fx. unfold ss_op. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold op_regions, op_stack, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP,
      op_ps_region, OPEN_SPAN.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. fold E. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * fold E. rewrite (VBI 1%nat ltac:(lia)).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 15) 0) (VAL (A_OBJ 15)));
      [cbn [sv_denot]; rewrite (EIMG 15%nat ltac:(lia)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | pose proof (pa_val_range (A_OBJ 15)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot).
    * fold E. rewrite (VBI 15%nat ltac:(lia)).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 15)) 0 8 OBx SB_OP);
      [cbn [sv_denot OBx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB_OP; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
    * fold E. rewrite (VBI 0%nat ltac:(lia)).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 16) 0) (VAL (A_OBJ 16)));
      [cbn [sv_denot]; rewrite (EIMG 16%nat ltac:(lia)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | pose proof (pa_val_range (A_OBJ 16)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kguar).
    * fold E. rewrite (VBI 16%nat ltac:(lia)).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 16)) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) memc _ _ Kuar).
    * fold E. rewrite (VB 10%nat ps E10) by (unfold in_app in Hfapp; lia).
      split; [lia|]. split; [unfold in_app in Hfapp; lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply HPS. lia.
  + apply pairwise_disjoint_of_extents.
    unfold op_regions, op_stack, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP,
      op_ps_region, OPEN_SPAN, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    fold E. rewrite !VBI by lia. rewrite (VB 10%nat ps E10) by (unfold in_app in Hfapp; lia).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold off_img, in_app, pcap_img_end, YImgTop.IMG_LO, YImgTop.IMG_TOP in *.
    revert Hslo Hshi H47 Hceil C1 C3 HTS Hstk0 HcellR HgotR HguarR HuarR Hsep Hfa1 Hfa2 Hf4096 Hfceil Hfapp Hfimg
      Hwlo Hwhi.
    clear. intros. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [op_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    fold E. rewrite Usp, U10, E32, !unsigned_lit_small by (unfold SB_OP; lia).
    try change (2 ^ 4) with 16. try change (2 ^ 3) with 8. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
    unfold in_app in Hfapp.
    revert Hslo Hshi H47 Hceil C1 C3 HTS Hstk0 Hal16 Hps8 Hfa1 Hfa2 Hf4096 Hfceil Hfapp Hwlo Hwhi.
    clear. unfold SB_OP. intros. repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
- apply (shent_op_ok _ _ ps).
  + unfold OBx. rewrite (U_atom _ 32 SB_OP E32) by (unfold SB_OP; lia). reflexivity.
  + rewrite (U_atom _ 10 ps E10) by (unfold in_app in Hfapp; lia). reflexivity.
  + unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
  + rewrite <- (aview_rd_of SEGS). exact Hsh.
Qed.

End c.



Section e.
Variable B : asyms.
Variable K : asource_syms.
Variable MT : ameter_ops.
Variable FM_RA : Z.
Variable CTX : list (list Z).
Variable roimg : (word -> option byte) -> Prop.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASM1 : astack_malloc_realizes SEGS B 1.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis MLAW : ameter_laws MT.
Hypothesis MLAWF : ameter_fs_laws MT.
Hypothesis FM : asrc_file_meter SK SEGS B MT.
Hypothesis FOPEN : tlibreac_fuzz_fopen_specX SK SEGS (BASE + AF_libreac_fuzz_fopen)
  (VAL (A_OBJ 3)) (VAL (A_OBJ 4)) (VAL (A_OBJ 2)) roimg B K MT FM_RA CTX.
Hypothesis AFREAD : afread_spec SK SEGS B K (SIGMA PS___interceptor_trampoline_fread).
Variable ra_fc1 ra_fc2 : Z.
Hypothesis AFCLOSE : afclose_source_spec SK SEGS B K (SIGMA PS___interceptor_trampoline_fclose) ra_fc1 ra_fc2
  pa_relro_lo pa_relro_hi.
Hypothesis HUfc1 : In [pc_free_ra0 (as_code B); ra_fc1] (as_universe B).
Hypothesis HUfc2 : In [pc_free_ra0 (as_code B); ra_fc2] (as_universe B).
Hypothesis ASIL : asource_img_laws SK SEGS B K.
(* The listing's object 12 is the "rb" mode literal (0x812e8 auipc, 0x812ec addi; 0x20d40 on the pin). *)
Hypothesis HMODE : VAL (A_OBJ 12) = as_mode K.
(* roimg reads only image bytes outside the runtime's statics, errno and the open-file list head. *)
Hypothesis ROK : forall (W : world SEGS) (m m' : word -> option byte),
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     ~ (AOFL_HEAD <= a < AOFL_HEAD + 8) -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  roimg (mrestrict (w_H W) m) -> roimg (mrestrict (w_H W) m').
(* The path literal's shadow, as a law of every AR state, because no kit clause keeps it across the frame
   request: the shadow byte of an image address is `aowned` (YG0n.v:241, the lm_zone (0, kLowMemEnd) entry of
   aowned covers the whole low shadow), so __asan_stack_malloc_1's own kept clause (YG0d.v:298-299, which keeps
   only ~aowned bytes) and acall_kept (YCbq.v:822-833, whose clauses are ceiling+ / blocks / image / frames and
   their shadow) both pass it over, and range_addressable_kept_win (YC85.v:355) wants the written window above
   kHighShadowEnd, which the frame's shadow write breaks. The instance discharges it from the literal's
   as_zero_shadow range through AR_zshadow_law (YG0d.v:435-438); lib/A's walk takes the same hypothesis under
   this name, discharged by a Theorem Labs lane at AF0m intake from Tfib_const_shadow / Tfib_zero_shadow (ts_const / ts_zsh)
   (a Theorem Labs lane, 2026-10-29 00:5xZ). *)
Hypothesis HPATH : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (VAL (A_OBJ 3)) 13 /\
  shadow_hull_vis (aview SEGS (w_H W) mem) (VAL (A_OBJ 3)) 13.
(* The two globals the call reads through libreac_fuzz_fopen (object 4 = g_file_len 0x5d3e40, object 2 = g_file
   0x5d3e60) are image bytes that are not the runtime's own statics and not errno: the harness's contract states
   the same of them (lib/A/Prog/PcapEntryDefs.v:366, 395 `gx_ok SEGS B pe_G` over G = 0x5d3f40.. / 0x5d3f60.. of
   the ASan pin). Without it the frame request's kept clauses say nothing about them (ajournal's image clause and
   acall_kept's both exclude as_owned_static and errno). *)
Hypothesis HGX : forall a, (VAL (A_OBJ 4) <= a < VAL (A_OBJ 4) + 8) \/ (VAL (A_OBJ 2) <= a < VAL (A_OBJ 2) + 8) ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
(* The read-only bytes lie below the open-file list head, for arodata_ok_journalP (PcapBase.v:23's class);
   lib/A's walks take it the same way (lib/A/Prog/PcapHarnessTail.v:37 HRO). *)
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
(* No kit lemma is bound with Let here: a Let-bound run lemma makes every symbolic run of the Section slow
   (measured by the PcapEntryKit lane: 9 s -> 17 min); each call site names its lemma. *)

(* What the caller keeps across the head: the three steps before the call of libreac_fuzz_fopen, each already
   reduced to its three clauses (ceiling+ outside this call's window, the image, the caller's blocks and
   frames), and then the callee's own journal. The shape follows lib/B/Prog/PcapSourceClose.v:332-396
   (tclose_kept_call). The written set is empty: up to the fopen return the walk writes only its own machine
   frame, its new frame F, F's shadow and the slot *(s1), never a byte of the caller's. *)
Lemma topen_kept_call : forall lyc Sc (W : world SEGS) memc mdc S2 mem1 (mdq : Model)
    ly3 S3 (W3 : world SEGS) mem3 md3 sp sp1 fpos,
  AR SEGS B lyc Sc W memc mdc ->
  frames S2 = (OP_CID, fpos) :: frames Sc ->
  (forall b0 m0, In (b0, m0) (ablocks B lyc Sc) -> In (b0, m0) (ablocks B lyc S2)) ->
  (forall b0 m0, In (b0, m0) (ablocks B lyc Sc) -> In (b0, m0) (ablocks B ly3 S3)) ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - TPCAP_SOURCE_OPEN_STK <= a < sp) ->
     aview SEGS (w_H W) mem1 a = aview SEGS (w_H W) memc a) ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     aview SEGS (w_H W) mem1 a = aview SEGS (w_H W) memc a) ->
  (forall b0 m0 i, In (b0, m0) (ablocks B lyc Sc) -> 0 <= i < req_size m0 ->
     aview SEGS (w_H W) mem1 (b0 + i) = aview SEGS (w_H W) memc (b0 + i)) ->
  (forall cid' pos' a, In (cid', pos') (frames Sc) ->
     (in_zr a (frame_rng lyc (cid', pos')) \/
      in_zr a (shadow_addr (frame_addr lyc cid' pos'), fs_frame_bytes cid' / 8)) ->
     aview SEGS (w_H W) mem1 a = aview SEGS (w_H W) memc a) ->
  ajournal SEGS B LIBREAC_FUZZ_FOPEN_STK sp1 afmemopen_fp lyc S2 W mem1 mdq [] ly3 S3 W3 mem3 md3
    EV_FUZZ_FOPEN ->
  (forall a, sp - TPCAP_SOURCE_OPEN_STK <= a < sp -> apresent (w_H W3) mem3 a) ->
  alloc_ceiling + TPCAP_SOURCE_OPEN_STK <= sp -> sp - 112 <= sp1 -> sp1 + 96 <= sp ->
  topen_kept SK SEGS B lyc Sc W memc W3 mem3 (sp - TPCAP_SOURCE_OPEN_STK) sp (fun _ => False).
Proof.
intros lyc Sc W memc mdc S2 mem1 mdq ly3 S3 W3 mem3 md3 sp sp1 fpos
  HAR Hfrs2 Hb12 Hb13 UNhi UNimg UNblk UNfrm HJf Hpw Hsp Hsp1lo Hsp1hi.
pose proof HJf as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & G4 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : TPCAP_SOURCE_OPEN_STK = 18736) by reflexivity.
assert (HFS : LIBREAC_FUZZ_FOPEN_STK = 18624) by reflexivity.
assert (K1 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - TPCAP_SOURCE_OPEN_STK <= a < sp) ->
  aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W) memc a).
{ intros a Ha Hn.
  transitivity (aview SEGS (w_H W) mem1 a); [apply G1; lia|]. apply UNhi; [lia | exact Hn]. }
split; [exact K1|]. split; [|split; [|split; [|split]]].
- intros b0 m0 i Hb Hi _.
  destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b0 m0 HAR Hb) as (_ & Hb4096 & Hbceil & _).
  transitivity (aview SEGS (w_H W) mem1 (b0 + i)).
  + apply (G2 b0 m0 i (Hb12 b0 m0 Hb) (Hb13 b0 m0 Hb) Hi).
    intros Hf. apply in_fp_inFP in Hf. destruct Hf as (r & [<- | []] & Hr). cbn in Hr. lia.
  + exact (UNblk b0 m0 i Hb Hi).
- intros a Hi Hno He Hof.
  transitivity (aview SEGS (w_H W) mem1 a); [apply (G3 a Hi Hno He); apply fp_spares_off; exact Hof|].
  apply UNimg; assumption.
- intros cid' pos' a Hin' Hr _.
  destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid' pos' HAR Hin') as (Hg4096 & Hgceil & Hgapp).
  pose proof (fs_frame_bytes_nonneg cid') as Hnn.
  pose proof (shadow_addr_bounds (frame_addr lyc cid' pos') ltac:(lia)) as Hsb1.
  transitivity (aview SEGS (w_H W) mem1 a).
  + apply (G4 cid' pos' a ltac:(rewrite Hfrs2; right; exact Hin')); [exact Hr|].
    intros Hf. apply in_fp_inFP in Hf. destruct Hf as (r & [<- | []] & Hrr). cbn in Hrr.
    unfold frame_rng, in_zr, shadow_addr, SHADOW_OFF in Hr. cbn [fst snd] in Hr. lia.
  + apply (UNfrm cid' pos' a Hin' Hr).
- intros a Ha Hn Hp. eapply (apresent_transfer SEGS);
    [lia | intros Him; pose proof (pa_segs_low a Him); lia | apply K1; [exact Ha | exact Hn] | exact Hp].
- exact Hpw.
Qed.


(* ---- the checkpoint at the call of libreac_fuzz_fopen (0x812f4) -----------------------------------
   What the walk has established when the call is taken: the caller's journal with this call's class-1 frame on
   top, the registers libreac_fuzz_fopen reads and the ones the body still needs, the frame's own words (header,
   flag pointer, the sixteen shadow bytes, the unwinder slot) and the machine frame, what is kept of the caller's
   memory (above the ceiling, the image, the caller's blocks, its frames and their shadow, the layout's extra
   ranges, and ps, which this walk does not write), the frame geometry, the call chain, and libreac_fuzz_fopen's
   own premises at that state. op_to_call proves it; head_to_fopen consumes it, makes the call and assembles
   op_fopen_ret (PcapSourceOpenPhF.v), so no symbolic state crosses the boundary. F, FL and sp1 are the frame,
   its flag and the realigned stack pointer, named as scalars so the walk past the call needs no let-bound
   definition of the Ph file's oF / oFL / osp1. *)
Definition op_at_call (cx : ocx) (fpos F FL sp1 : Z) (S2 : astate) (regsc : bvmap 5 word)
  (memc2 : word -> option byte) (md : Model) : Prop :=
  let STK := o_STK cx in let sp0 := o_sp0 cx in let FP := o_FP cx in let ly := o_ly cx in let S := o_S cx in
  let W0 := o_W0 cx in let mem0 := o_mem0 cx in let md0 := o_md0 cx in let own := o_own cx in
  let lyc := o_lyc cx in let Sc := o_Sc cx in let W := o_W cx in let memc := o_memc cx in
  let mdc := o_mdc cx in let k := o_k cx in let regs := o_regs cx in let ch := o_ch cx in
  let ps := o_ps cx in let n := o_n cx in let b := o_b cx in let C := o_C cx in
  let cid := o_cid cx in let pos := o_pos cx in
  let rd2 := aview SEGS (w_H W) memc2 in
  F = oF cx fpos /\ FL = oFL cx fpos /\ sp1 = osp1 cx /\
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 ((OP_CID, fpos) :: own) lyc S2 W memc2 md k /\
  frames S2 = (OP_CID, fpos) :: frames Sc /\ ~ In (OP_CID, fpos) (frames Sc) /\
  st_nev S2 = st_nev Sc /\ blocks_bytes S2 = blocks_bytes Sc /\
  ablocks B lyc S2 = ablocks B lyc Sc /\ (exists f, S2 = set_fs f Sc) /\
  (* the registers at the call *)
  spZ regsc = sp1 /\ s0Z regsc = spZ regs /\ getr regsc 1 = w64 (BASE + OP_RET_FOPEN) /\
  getr regsc 3 = getr regs 3 /\ getr regsc 4 = getr regs 4 /\ getr regsc 9 = w64 sp1 /\
  getr regsc 10 = w64 (VAL (A_OBJ 3)) /\ getr regsc 11 = w64 (as_mode K) /\
  getr regsc 18 = w64 F /\ getr regsc 19 = w64 ps /\ getr regsc 20 = w64 (VAL (A_OBJ 3)) /\
  getr regsc 21 = w64 (SHADOW_OFF + F / 8) /\ getr regsc 22 = w64 F /\ getr regsc 23 = w64 SHADOW_OFF /\
  getr regsc 25 = getr regs 25 /\ getr regsc 26 = getr regs 26 /\ getr regsc 27 = getr regs 27 /\
  (* the words in memory *)
  rdword rd2 (spZ regs - 8) = Some (raZ regs) /\
  (forall j, 0 <= j < 10 -> rdword rd2 (spZ regs - 16 - 8 * j) =
     Some (bv_unsigned (getr regs (Z_to_bv 5 (if j <? 2 then 8 + j else 16 + j))))) /\
  rdword rd2 F = Some OP_MAGIC /\ rdword rd2 (F + 8) = Some (VAL (A_OBJ 10)) /\
  rdword rd2 (F + 16) = Some (VAL (A_OBJ 11)) /\ rdword rd2 (F + OP_FLAGPTR) = Some FL /\
  (forall i, (i < 16)%nat -> rd2 (SHADOW_OFF + F / 8 + Z.of_nat i) = Some (nth i OSH_out 0)) /\
  rdword rd2 sp1 = Some F /\
  (forall a, F <= a < F + fs_frame_bytes OP_CID -> apresent (w_H W) memc2 a) /\
  (* what is kept of the caller *)
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs - TPCAP_SOURCE_OPEN_STK <= a < spZ regs) ->
     rd2 a = aview SEGS (w_H W) memc a) /\
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
     ~ (as_errno B <= a < as_errno B + 4) -> rd2 a = aview SEGS (w_H W) memc a) /\
  (forall b0 m0 i, In (b0, m0) (ablocks B lyc Sc) -> 0 <= i < req_size m0 ->
     rd2 (b0 + i) = aview SEGS (w_H W) memc (b0 + i)) /\
  (forall cid' pos' a, In (cid', pos') (frames Sc) ->
     (in_zr a (frame_rng lyc (cid', pos')) \/
      in_zr a (shadow_addr (frame_addr lyc cid' pos'), fs_frame_bytes cid' / 8)) ->
     rd2 a = aview SEGS (w_H W) memc a) /\
  (forall a, Exists (in_zr a) (ly_extra lyc) -> ~ (as_errno B <= a < as_errno B + 4) ->
     rd2 a = aview SEGS (w_H W) memc a) /\
  (forall i, 0 <= i < 24 -> rd2 (ps + i) = aview SEGS (w_H W) memc (ps + i)) /\
  range_addressable rd2 SHADOW_OFF ps 24 /\
  m_fds md = m_fds mdc /\ m_fs md = m_fs mdc /\
  (* the frame's geometry and the realigned stack pointer *)
  4096 <= F /\ F + fs_frame_bytes OP_CID <= alloc_ceiling /\ F mod 64 = 0 /\
  (F + fs_frame_bytes OP_CID <= frame_addr lyc cid pos \/
   frame_addr lyc cid pos + fs_frame_bytes cid <= F) /\
  alloc_ceiling <= sp1 /\ sp1 + 96 <= spZ regs /\ spZ regs - 112 <= sp1 /\ sp1 mod 16 = 0 /\
  (* the chain and the callee's premises *)
  achain lyc rd2 sp1 (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch) /\
  roimg (mrestrict (w_H W) memc2) /\
  range_addressable rd2 SHADOW_OFF (VAL (A_OBJ 3)) 13 /\ shadow_hull_vis rd2 (VAL (A_OBJ 3)) 13 /\
  val_mem SEGS (mrestrict (w_H W) memc2) (VAL (A_OBJ 4)) 8 n /\
  val_mem SEGS (mrestrict (w_H W) memc2) (VAL (A_OBJ 2)) 8 b /\
  asource_none SEGS K (mrestrict (w_H W) memc2) /\
  (1 <= n -> In (b, n) (ablocks B lyc S2) /\ garr8 SEGS (mrestrict (w_H W) memc2) b C /\ bytes_ok C) /\
  mo_ok MT S2 (mo_malloc MT SRC_FILE_BLOCK) /\ st_nev S2 + EV_FUZZ_FOPEN <= EV_MAX /\
  blocks_bytes S2 + SRC_FILE_BLOCK <= LIVE_MAX.

(* The walk from the entry 0x811e0 to the call 0x812f4: the prologue, the use-after-return flag (0x81234, taken
   as 1, so 0x81240 is not taken), the class-1 frame request (__asan_stack_malloc_1 at 0x81248; count_cid and the
   apath premise are discharged inside aj_stack_malloc_atS, so 0x8125c is taken and the machine-frame arm
   0x81260..0x81278 is dead), the unwinder slot, the frame header, its twelve shadow bytes and the mode literal. *)
Lemma op_to_call : forall cx, op_pre SK B K MT FM_RA CTX roimg cx ->
  SRr SEGS (o_W cx) (cfg_at SEGS (BASE + AF_pcap_source_open) (o_regs cx) (o_memc cx) (o_mdc cx))
    (fun W2 c2 => W2 = o_W cx /\ exists fpos F FL sp1 S2 regsc memc2 md,
       c2 = mkCfg (mkst regsc (w64 (BASE + AF_libreac_fuzz_fopen)) memc2 (seg_rom SEGS)) md /\
       op_at_call cx fpos F FL sp1 S2 regsc memc2 md).
Proof.

intros cx Hpre.
destruct cx as [STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch ps n b M C cid pos].
unfold op_pre in Hpre. cbn [o_STK o_sp0 o_FP o_ly o_S o_W0 o_mem0 o_md0 o_own o_lyc o_Sc o_W o_memc o_mdc o_k
  o_regs o_ch o_ps o_n o_b o_M o_C o_cid o_pos] in Hpre |- *.
destruct Hpre as (HJ & HROD & Hraw & Hra4 & Hgp & Htp & H10 & H11 & Hch & Hctx & Hal16 & Hwlo & Hwhi & Htop32 & Hnfr
  & Hown & Hfa1 & Hfa2 & Hps0 & Hps8 & Hsh & HFP0 & HRO & HPra & HPhull & HVn & HVb & Hb64 & HNONE & Hn & HnC
  & Hinput & HMETA & Hev & Hlive & MOK & HU0 & HUC).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof (pa_base_lo (PL := PL_pcap) (PI := PI)) as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & Hnev & Hk0 & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (HTS : TPCAP_SOURCE_OPEN_STK = 18736) by reflexivity.
assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hf4096 & Hfceil & Hfapp).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hfapp.
pose proof (frm_off_imgP B lyc Sc W memc mdc cid pos HAR Hin) as Hfimg. unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in Hfimg.
pose proof (frame_al64 SEGS B lyc Sc W memc mdc cid pos HAR Hin) as (Hfa64 & Hfb64 & Hfb).
assert (HIE : pcap_img_end = (symaddr ImgPages.AsanUbsan.top)) by reflexivity.
Time destruct (op_entry B LAWS TL TLF STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ps cid pos
  HJ H10 Hal16 Hwlo Hwhi Hown Hin Hfa1 Hfa2 Hps8 Hsh) as [HS SHOK].
remember (Eimg (Ereg regs op_extra)) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs op_extra) n)
  by (intros nn Hn'; subst E; apply Eimg_low; exact Hn').
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 ps) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SB_OP) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (HAE : env_agree 32 (Ereg regs op_extra) E) by (split; [intros nn Hn'; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (Hps64 : 0 <= ps < 2 ^ 64) by lia.
assert (U10 : bv_unsigned (ew E 10) = ps) by (rewrite E10; apply unsigned_lit_small; exact Hps64).
clear HEdef EL.
unfold cfg_at. change (w64 (BASE + AF_pcap_source_open)) with (Z_to_bv 64 (BASE + AF_pcap_source_open)).
(* The prologue, the frame request, up to the call of __asan_stack_malloc_1 (0x81248). *)
Time paj_run_tok (paj_run (SK := SK) B LAWS) HS HJ SHOK OPspan;
  [ op_awr (spZ regs) sp0 Usp |].
(* The prologue writes only the machine frame [sp0' - 112, sp0') (it never touches ps or any shadow byte). *)
Time pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _
  (fun a => (spZ regs - 112 <= a < spZ regs)) HFr
  ltac:(intros bbW wloW whiW aW HinW HrrW; vm_compute in HinW;
        repeat (destruct HinW as [HqW | HinW];
          [injection HqW as <- <- <-; cbn [base_val] in HrrW; rewrite ?Usp, ?U10 in HrrW; lia|]);
        destruct HinW)) as UN1.
Time pmkst HS.
Time prreg HS (2%bv : bv 5) R2. prreg HS (1%bv : bv 5) R1.
Time prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
(* s1 = sp = (sp0' - 96) & -32 (0x81218). *)
set (sp1 := 32 * ((spZ regs - OPEN_FRAME) / 32)).
destruct (sp1_facts (spZ regs - OPEN_FRAME) ltac:(unfold OPEN_FRAME; lia)
  ltac:(unfold OPEN_FRAME; rewrite Zminus_mod, Hal16; reflexivity)) as (Hsp1r & Hsp1al32 & Hsp1al16).
fold sp1 in Hsp1r, Hsp1al32, Hsp1al16. unfold OPEN_FRAME in Hsp1r.
assert (Rsp1 : getr (ms_regs ms) 2 = Z_to_bv 64 sp1).
{ rewrite R2.
  change (alu64 ALU_AND (Z_to_bv 64 (bv_unsigned (ew E 2) + -96)) (Z_to_bv 64 (-32)))
    with (sv_denot E (SAlu ALU_AND (SOff 2 (-96)) (SLit (-32)))).
  rewrite (denot_and_m32 E 2 (spZ regs) (-96)); [unfold sp1, OPEN_FRAME; f_equal; lia | | lia | lia | lia].
  rewrite <- Usp. symmetry. apply Z_to_bv_bv_unsigned. }
(* The trimmed machine frame (the saves, sp0' - 88 .. sp0'; the callee's window starts at s1 <= sp0' - 96) and ps;
   the GOT words and the two runtime cells are not read again. *)
Time lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
  let rs := eval vm_compute in (ss_mem ssx) in
  let rs' := eval vm_compute in (pick (trim_stack rs (-88) 0) [0; 5]%nat) in
  pose proof (st_ok_submem SEGS Ex ssx msx rs' HS ltac:(cbn [ss_mem setpc]; submem_to) ltac:(vm_compute; reflexivity))
    as HS2; clear HS; rename HS2 into HS end.
cbn [ss_pc ss_regs ss_resv ss_facts setpc] in HS.
(* __asan_stack_malloc_1(0x60) (0x81248): the class-1 slot fpos on top of own. Its window is ESTACK below s1:
   ESTACK - (s1 - sp0) <= STK because s1 >= sp0' - 112 and sp0' - TPCAP_SOURCE_OPEN_STK >= sp0 - STK.
   Its two caller premises: count_cid 1 (frames Sc) < fs_frames 1 from op_pre's length (frames Sc) <= 7
   (count_cid_le_length) and 8 <= fs_frames 1; the progress premise is op_SMP, inside aj_stack_malloc_atS. *)
rewrite (palf_sm1 B TLF).
pose proof (count_cid_le_length 1 (frames Sc)) as Hcnt.
assert (HFF : 8 <= fs_frames 1) by (vm_compute; congruence).
Time eapply SRr_bind.
{ eapply (aj_stack_malloc_atS SEGS B LAWS Hsegs (pal_env B TL) ML (op_SMP B) 1 ASM1 ltac:(lia) W (ms_regs ms) (ms_mem ms)
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k (sp1 - sp0) _ HJ).
  - unfold spZ at 1. rewrite Rsp1, unsigned_lit_small by lia. lia.
  - rewrite Zminus_mod, Hsp1al16, Hsp0al. reflexivity.
  - lia.
  - change ESTACK with 4096. lia.
  - rewrite R3, E3. exact Hgp.
  - rewrite R4, E4. exact Htp.
  - exact R1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - lia. }
cbv beta. clear R2 R3 R4 R1.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz
  & Hflag & HK & HJe & (fS2 & ES2)).
replace (sp0 + (sp1 - sp0)) with sp1 in HK, HJe by lia. change ESTACK with 4096 in HK.
pose proof HJ2 as (HAR2 & Hly2 & _).
assert (Hfin2 : In (1, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
assert (HinS2 : In (cid, pos) (frames S2)) by (rewrite Hfrs2; right; exact Hin).
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
Time jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp; intros a Ha.
    + apply (mbyte_of_aview SEGS). pose proof HK as (K1 & _). apply K1; lia.
    + intros _. apply (apresent_writable SEGS). apply Hpres2. lia.
  - eapply (region_kept_ownframe_aj SEGS B); [exact HK | exact U10 | exact Hin | left; lia | intros ?a ?Ha [] |].
    intros a Ha. refine (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ2 _)).
    right. right. right. exists cid, pos. split; [right; exact Hown|]. left. unfold in_zr. cbn [fst snd]. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 40 (map (getr regs2) CLOB)) as Ev1 eqn:HE1 in HS.
assert (HEI1 : img_env VAL A_LIM Ev1) by (rewrite HE1; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD1 : forall nn, (nn < 40)%nat -> ew Ev1 nn = ew E nn) by (intros nn Hnn; rewrite HE1; apply YN3v.ew_havoc_old; exact Hnn).
assert (HAE1 : env_agree 32 (Ereg regs op_extra) Ev1) by (rewrite HE1; apply env_agree_havoc_ge; [lia | exact HAE]).
clear HE1.
(* The frame F (a0 after the call, atom 44), its flag FL and its shadow. *)
set (F := frame_addr lyc 1 fpos) in *. set (FL := flag_addr lyc 1 fpos) in *.
Time prreg HS (10%bv : bv 5) R10.
assert (E44 : ew Ev1 44 = Z_to_bv 64 F) by (rewrite <- R10, Ha0; reflexivity). clear R10.
destruct (frames_bounds SEGS B LAWS lyc S2 W mem2 md2 1 fpos HAR2 Hfin2) as (HF4096 & HFceil & HFapp).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. fold F in HF4096, HFceil, HFapp.
pose proof (frame_al64 SEGS B lyc S2 W mem2 md2 1 fpos HAR2 Hfin2) as (HFa64 & _ & _). fold F in HFa64.
pose proof (frm_off_imgP B lyc S2 W mem2 md2 1 fpos HAR2 Hfin2) as HFimg. unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in HFimg.
fold F in HFimg.
change (fs_frame_bytes 1) with 128 in *.
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR2 Hfin2) as (_ & _ & HFpres & HFSpres).
change (fs_frame_bytes 1) with 128 in HFpres, HFSpres. fold F in HFpres, HFSpres.
destruct (FFL lyc S2 W mem2 md2 1 fpos HAR2 Hfin2) as (HFLpres & HFLown & HFLrng). fold FL in HFLpres, HFLown, HFLrng.
(* F and the caller's frame holding ps are two frames of S2: disjoint. *)
assert (HdFps : F + 128 <= frame_addr lyc cid pos \/ frame_addr lyc cid pos + fs_frame_bytes cid <= F).
{ destruct (in_split _ _ Hin) as (l2 & l3 & El).
  pose proof (sep_frames_pos SEGS B LAWS lyc S2 W mem2 md2 (1, fpos) (cid, pos) [] l2 l3 HAR2
    ltac:(rewrite Hfrs2, El; reflexivity)) as Hd.
  unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. fold F in Hd. change (fs_frame_bytes 1) with 128 in Hd. lia. }
(* s1 and sp: rebind them to the atom 60 = sp1 (the engine cannot place a store through a masked address). *)
assert (E12 : ew Ev1 2 = Z_to_bv 64 (spZ regs)) by (rewrite OLD1 by lia; rewrite E2; symmetry; apply Z_to_bv_bv_unsigned).
Time prreg_raw HS (2%bv : bv 5) Rsp2. prreg_raw HS (9%bv : bv 5) Rs12.
rewrite (denot_and_m32 Ev1 2 (spZ regs) (-96) E12) in Rsp2 by lia.
rewrite (denot_and_m32_add0 Ev1 2 (spZ regs) (-96) E12) in Rs12 by lia.
replace (32 * ((spZ regs + -96) / 32)) with sp1 in Rsp2, Rs12 by (unfold sp1, OPEN_FRAME; f_equal; f_equal; lia).
pose proof (st_ok_pi_havoc_hi 60 Ev1 _ _ [Z_to_bv 64 sp1] HS ltac:(vm_compute; reflexivity)) as HS3.
clear HS. rename HS3 into HS.
remember (havoc Ev1 60 [Z_to_bv 64 sp1]) as E2v eqn:HE2 in HS.
assert (OLD2 : forall nn, (nn < 60)%nat -> ew E2v nn = ew Ev1 nn) by (intros nn Hnn; rewrite HE2; apply YN3v.ew_havoc_old; exact Hnn).
assert (E60 : ew E2v 60 = Z_to_bv 64 sp1) by (rewrite HE2; exact (ew_havoc_new Ev1 60 [Z_to_bv 64 sp1] 0 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (HEI2 : img_env VAL A_LIM E2v) by (rewrite HE2; apply img_env_havoc; [exact HEI1 | cbv; lia]).
assert (HAE2 : env_agree 32 (Ereg regs op_extra) E2v) by (rewrite HE2; apply env_agree_havoc_ge; [lia | exact HAE1]).
clear HE2.
Time lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (2%bv : bv 5) (SOff 60 0) HS ltac:(vm_compute; reflexivity)
    ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E60, Z.add_0_r, Z_to_bv_bv_unsigned; symmetry; exact Rsp2)) as HS3 end.
clear HS; rename HS3 into HS.
Time lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (9%bv : bv 5) (SOff 60 0) HS ltac:(vm_compute; reflexivity)
    ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E60, Z.add_0_r, Z_to_bv_bv_unsigned; symmetry; exact Rs12)) as HS3 end.
clear HS; rename HS3 into HS.
(* The flag FL (atom 61) and the shadow SH = SB + F / 8 (atom 62). *)
pose proof (st_ok_pi_havoc_hi 61 E2v _ _ [Z_to_bv 64 FL; Z_to_bv 64 (SB_OP + F / 8)] HS ltac:(vm_compute; reflexivity)) as HS3.
clear HS. rename HS3 into HS.
remember (havoc E2v 61 [Z_to_bv 64 FL; Z_to_bv 64 (SB_OP + F / 8)]) as E3v eqn:HE3 in HS.
assert (OLD3 : forall nn, (nn < 61)%nat -> ew E3v nn = ew E2v nn) by (intros nn Hnn; rewrite HE3; apply YN3v.ew_havoc_old; exact Hnn).
assert (E61 : ew E3v 61 = Z_to_bv 64 FL)
  by (rewrite HE3; exact (ew_havoc_new E2v 61 [Z_to_bv 64 FL; Z_to_bv 64 (SB_OP + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (E62 : ew E3v 62 = Z_to_bv 64 (SB_OP + F / 8))
  by (rewrite HE3; exact (ew_havoc_new E2v 61 [Z_to_bv 64 FL; Z_to_bv 64 (SB_OP + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (HEI3 : img_env VAL A_LIM E3v) by (rewrite HE3; apply img_env_havoc; [exact HEI2 | cbv; lia]).
assert (HAE3 : env_agree 32 (Ereg regs op_extra) E3v) by (rewrite HE3; apply env_agree_havoc_ge; [lia | exact HAE2]).
clear HE3.
assert (E3_2 : ew E3v 2 = Z_to_bv 64 (spZ regs)) by (rewrite OLD3, OLD2 by lia; exact E12).
assert (E3_10 : ew E3v 10 = Z_to_bv 64 ps) by (rewrite OLD3, OLD2, OLD1 by lia; exact E10).
assert (E3_32 : ew E3v 32 = Z_to_bv 64 SB_OP) by (rewrite OLD3, OLD2, OLD1 by lia; exact E32).
assert (E3_44 : ew E3v 44 = Z_to_bv 64 F) by (rewrite OLD3, OLD2 by lia; exact E44).
assert (E3_60 : ew E3v 60 = Z_to_bv 64 sp1) by (rewrite OLD3 by lia; exact E60).
assert (Hsp1_hi : sp1 + 96 <= spZ regs) by lia.
assert (Hsp1_lo : alloc_ceiling <= sp1) by lia.
assert (HF8 : (SB_OP + F / 8) mod 8 = 0).
{ unfold SB_OP. pose proof (Z_div_mod_eq_full F 64) as D. rewrite HFa64, Z.add_0_r in D.
  assert (F / 8 = 8 * (F / 64)) as ->.
  { rewrite D at 1. replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by lia. apply Z.div_mul. lia. }
  rewrite Z.add_mod by lia. rewrite (Z.mul_comm 8), Z.mod_mul by lia. reflexivity. }
Time add_fact HS 60%nat (mkAF (2 ^ 46) (2 ^ 47) 5)
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E3_60, unsigned_lit_small by lia; change (2 ^ 5) with 32; repeat split; lia).
Time add_fact HS 44%nat (HPTR 6)
  ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E3_44, unsigned_lit_small by lia; change (2 ^ 6) with 64; repeat split; lia).
Time add_fact HS 61%nat (HPTR 0)
  ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E61, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; repeat split; lia).
assert (HFb : 4096 <= F /\ F + 128 <= 140737479966720) by (clear - HF4096 HFceil C1; lia).
assert (HF8b : 0 <= F / 8 <= 2 ^ 44).
{ split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]. }
assert (HA62 : afact_ok E3v 62 (mkAF SB_OP (SB_OP + 2 ^ 44) 3)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E62.
  rewrite unsigned_lit_small by (unfold SB_OP; clear - HF8b; lia).
  change (2 ^ 3) with 8. split; [|split; [exact HF8 | lia]]. unfold SB_OP. clear - HF8b. lia. }
Time add_fact HS 62%nat (mkAF SB_OP (SB_OP + 2 ^ 44) 3) ltac:(exact HA62).
Time lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_pi_add_alias Ev ssx msx _ _ HS (shadow_decl_ok Ev 44 32 62 F SB_OP E3_44 ltac:(lia) E3_32 E62)) as HS3 end.
clear HS; rename HS3 into HS; norm_pi HS.
assert (U3sp : bv_unsigned (ew E3v 2) = spZ regs) by (rewrite E3_2; apply unsigned_lit_small; lia).
assert (U3_10 : bv_unsigned (ew E3v 10) = ps) by (rewrite E3_10; apply unsigned_lit_small; lia).
assert (U44 : bv_unsigned (ew E3v 44) = F) by (rewrite E3_44; apply unsigned_lit_small; lia).
assert (U60 : bv_unsigned (ew E3v 60) = sp1) by (rewrite E3_60; apply unsigned_lit_small; lia).
assert (U62 : bv_unsigned (ew E3v 62) = SB_OP + F / 8) by (rewrite E62; apply unsigned_lit_small; unfold SB_OP; lia).
(* The frame's bytes (atom 44, the flag pointer in its last word), its 16 shadow bytes (atom 62, all 0 as
   __asan_stack_malloc_1 leaves them) and the slot *(s1) (atom 60, 0x8127c). *)
assert (HF8eq : F = 8 * (F / 8)).
{ pose proof (Z_div_mod_eq_full F 64) as D. rewrite HFa64, Z.add_0_r in D.
  rewrite D at 2. replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by lia. rewrite Z.div_mul by lia. lia. }
assert (HSH0 : forall j, 0 <= j < 2 -> val_mem SEGS (mrestrict (w_H W) mem2) (SB_OP + F / 8 + 8 * j) 8 0).
{ intros j Hj. apply val_mem_zero8. intros i Hi. unfold zero_shadow, shadow_of_addr in Hz.
  replace (SB_OP + F / 8 + 8 * j + i) with (SHADOW_OFF + F / 8 + (8 * j + i)) by (unfold SB_OP, SHADOW_OFF; lia).
  apply Hz. change (128 / 8) with 16. lia. }
Time lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_pi_add_region Ev ssx msx (fframe_region 44 61 1 []) HS eq_refl
    ltac:(unfold region_ok, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
          change (fs_frame_bytes 1) with 128; rewrite U44; split; [lia|]; split; [lia|]; split;
          [ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia)))
          | apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val SEGS Ev _ F (128 - 8) 8 _ FL);
            [cbn [sv_denot]; rewrite E61, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside
            | replace (F + (128 - 8)) with (F + 128 - 8) by lia; exact (val_mem_of_rdword SEGS _ _ _ _ Hflag)] ])
    ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
          cbn [all_disjoint]; unfold extent_disjoint, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
          change (fs_frame_bytes 1) with 128; rewrite ?U44, ?U3sp, ?U3_10;
          repeat split; lia)) as HS3 end.
clear HS; rename HS3 into HS; norm_pi HS.
Time lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_pi_add_region Ev ssx msx
    (fshadow_region 62 1 0 12 [YP09.mkChunk 0 (CVal 8 (SLit 0)); YP09.mkChunk 8 (CVal 8 (SLit 0))]) HS eq_refl
    ltac:(unfold region_ok, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
          change (fs_frame_bytes 1 / 8) with 16; rewrite U62; split; [unfold SB_OP; lia|]; split; [unfold SB_OP; lia|]; split;
          [ intros o Ho; apply (apresent_writable SEGS); unfold shadow_addr in HFSpres;
            replace (SB_OP + F / 8 + o) with (SHADOW_OFF + F / 8 + o) by (unfold SB_OP, SHADOW_OFF; lia);
            apply (proj1 (HFSpres o ltac:(change (128 / 8) with 16; lia)))
          | apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ (SB_OP + F / 8) 0 8 _ 0); [reflexivity | zside | zside | rewrite Z.add_0_r; replace (SB_OP + F / 8) with (SB_OP + F / 8 + 8 * 0) by lia; apply HSH0; lia]|];
            apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ (SB_OP + F / 8) 8 8 _ 0); [reflexivity | zside | zside | replace (SB_OP + F / 8 + 8) with (SB_OP + F / 8 + 8 * 1) by lia; apply HSH0; lia]|];
            apply Forall_nil ])
    ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
          cbn [all_disjoint]; unfold extent_disjoint, fshadow_region, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
          change (fs_frame_bytes 1 / 8) with 16; change (fs_frame_bytes 1) with 128; rewrite ?U62, ?U44, ?U3sp, ?U3_10;
          unfold SB_OP; repeat split; lia)) as HS3 end.
clear HS; rename HS3 into HS; norm_pi HS.
Time lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_pi_add_region Ev ssx msx (YP09.mkRegion (Some 60%nat) 0 8 0 8 []) HS eq_refl
    ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
          rewrite U60; split; [lia|]; split; [lia|]; split; [|constructor];
          intros o Ho; apply (apresent_writable SEGS); apply Hpres2; lia)
    ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
          cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
          rewrite ?U62, ?U44, ?U3sp, ?U3_10, ?U60;
          unfold SB_OP; repeat split; lia)) as HS3 end.
clear HS; rename HS3 into HS; norm_pi HS.
(* The shadow entry of ps across the frame request: __asan_stack_malloc_1 keeps every shadow byte of the caller's
   own frames (acall_kept's frame clause with E = False). *)
assert (Hfa8 : frame_addr lyc cid pos = 8 * (frame_addr lyc cid pos / 8)) by (apply div8_eq64; exact Hfa64).
assert (Hfb8 : fs_frame_bytes cid = 8 * (fs_frame_bytes cid / 8)) by (apply div8_eq64; exact Hfb64).
Time assert (HRA2 : range_addressable (aview SEGS (w_H W) mem2) SHADOW_OFF ps 24).
{ apply (ra_frame (aview SEGS (w_H W) memc)); [exact Hsh|].
  intros x Hx. unfold shadow_of_addr. pose proof HK as (_ & _ & _ & K4 & _).
  pose proof (shadow_rng_in _ _ x Hfa8 Hfb8 ltac:(lia)) as Hrng.
  rewrite (K4 cid pos (SHADOW_OFF + x / 8) Hin
    ltac:(right; unfold in_zr, shadow_addr; cbn [fst snd]; lia) ltac:(intros [])).
  apply UN1; [unfold SHADOW_OFF; lia|].
  intros Hc; unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia. }
Time assert (SHOK3 : sh_ok SEGS OBx op_SH E3v (mrestrict (w_H W) mem2)).
{ apply (shent_op_ok _ _ ps).
  - unfold OBx. rewrite (U_atom _ 32 SB_OP E3_32) by (unfold SB_OP; lia). reflexivity.
  - rewrite (U_atom _ 10 ps E3_10) by lia. reflexivity.
  - unfold kLowShadowBeg, kHighMemBeg. lia.
  - rewrite <- (aview_rd_of SEGS). exact HRA2. }
clear SHOK.
(* The three write windows that are not the machine frame: this call's frame F, its 16 shadow bytes, and the
   caller's struct ps (a frame the caller's journal owns). *)
assert (HFrng : forall a, F <= a < F + 128 -> in_frames lyc ((1, fpos) :: own) a).
{ intros a Ha. exists 1, fpos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
  change (fs_frame_bytes 1) with 128. fold F. lia. }
assert (HSHrng : forall a, SB_OP + F / 8 <= a < SB_OP + F / 8 + 16 -> in_frames lyc ((1, fpos) :: own) a).
{ intros a Ha. exists 1, fpos. split; [left; reflexivity|]. right. unfold in_zr, shadow_addr. cbn [fst snd].
  change (fs_frame_bytes 1 / 8) with 16. fold F. unfold SB_OP, SHADOW_OFF in Ha |- *. lia. }
assert (HPSrng : forall a, ps <= a < ps + 24 -> in_frames lyc ((1, fpos) :: own) a).
{ intros a Ha. exists cid, pos. split; [right; exact Hown|]. left. unfold in_zr. cbn [fst snd]. lia. }
(* The prologue's frame_of is spent (HRA2 carries what the walk needs of it); the plain run rebinds the name. *)
clear HF HFr HG.
(* 0x8124c..0x812f0: s2 = s6 = F (the frame is real, so 0x8125c `bnez s2` is taken and the machine-frame arm
   0x81260..0x81278 is dead), *(s1) = F (0x8127c), the frame header (magic 0x41b58ab3 and the two descriptors,
   0x812a4..0x812ac) and the 12 shadow bytes (0x812b8..0x812e4), then the "rb" literal (0x812e8, 0x812ec).
   This stretch is walked by the PLAIN run: it stores into the shadow band, which the token engine's cells_safe_b
   refuses while a region's window lies in the band (YCbn.v:115-119); the token run resumes at the call, with the
   frame and its shadow read-only (cgif_file_fuzzer lib/A/ACbf.v:155-163 fs_ro). *)
Time paj_run_to_sh (SRr_run_to_pi_AJ (SK := SK) B LAWS) HS HJ2 (symaddr ((Symbols.AsanUbsan.s_pcap_source_open + 0x114) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z);
  [ op_awr (spZ regs) sp0 U3sp;
    first [ left; lia
          | right; right; right;
            first [ apply HFrng; lia | apply HSHrng; lia | apply HPSrng; lia ] ]
  |].
(* The stretch wrote only F, F's shadow, the slot *(s1) and the machine frame, so ps's shadow entry still holds. *)
Time pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _
  (fun a => (sp1 <= a < sp1 + 8) \/ (SB_OP + F / 8 <= a < SB_OP + F / 8 + 12) \/ (F <= a < F + 128)
            \/ (spZ regs - 88 <= a < spZ regs)) HFr
  ltac:(intros bbW wloW whiW aW HinW HrrW; vm_compute in HinW;
        repeat (destruct HinW as [HqW | HinW];
          [injection HqW as <- <- <-; cbn [base_val] in HrrW; rewrite ?U3sp, ?U3_10, ?U44, ?U60, ?U62 in HrrW; lia|]);
        destruct HinW)) as UN2.
cbn [ms_mem mkst] in UN2.
Time lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
  assert (SHOK4 : sh_ok SEGS OBx op_SH E3v (mrestrict (w_H W) (ms_mem msx)));
  [ clear_big; apply (shent_op_ok _ _ ps);
    [ unfold OBx; rewrite (U_atom _ 32 SB_OP E3_32) by (unfold SB_OP; lia); reflexivity
    | rewrite (U_atom _ 10 ps E3_10) by lia; reflexivity
    | unfold kLowShadowBeg, kHighMemBeg; lia
    | rewrite <- (aview_rd_of SEGS); apply (ra_frame (aview SEGS (w_H W) mem2)); [exact HRA2|];
      intros x Hx; unfold shadow_of_addr;
      pose proof (shadow_rng_in _ _ x Hfa8 Hfb8 ltac:(lia)) as Hrng2;
      destruct HdFps as [Hd | Hd];
      (apply UN2; [unfold SHADOW_OFF; lia|];
       intros [Hc | [Hc | [Hc | Hc]]];
       unfold SHADOW_OFF, SB_OP, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia) ]
  | ] end.
clear SHOK3.
(* The prologue's and this stretch's frame_of are spent (UN2 carries the stretch); the token run rebinds them. *)
clear HF HFr HG.
(* The frame and its shadow are written no more in this walk: closing their windows lets the token engine run
   (cells_safe_b). The token run executes the call 0x812f4 and stops at libreac_fuzz_fopen's entry. *)
Time set_ro HS 1%nat. set_ro HS 2%nat.
Time paj_run_tok (paj_run (SK := SK) B LAWS) HS HJ2 SHOK4 OPspan;
  [ op_awr (spZ regs) sp0 U3sp;
    first [ left; lia
          | right; right; right;
            first [ apply HFrng; lia | apply HSHrng; lia | apply HPSrng; lia ] ]
  |].
(* --- the fopen call 0x812f4 --------------------------------------------------------------------
   What the three steps so far kept of the entry memory memc: the bytes above the allocator's ceiling outside
   this call's own stack window, the image bytes that are not the runtime's statics or errno, and the bytes of
   the caller's live blocks. Each is a clause of acall_kept (the frame request) between two frame_of windows
   (the prologue and the stretch above). *)
Time pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _
  (fun a => (sp1 <= a < sp1 + 8) \/ (spZ regs - 88 <= a < spZ regs)) HFr
  ltac:(intros bbW wloW whiW aW HinW HrrW; vm_compute in HinW;
        repeat (destruct HinW as [HqW | HinW];
          [injection HqW as <- <- <-; cbn [base_val] in HrrW; rewrite ?U3sp, ?U3_10, ?U44, ?U60, ?U62 in HrrW; lia|]);
        destruct HinW)) as UN3.
cbn [ms_mem mkst] in UN3.
Time lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
  assert (HHI : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs - TPCAP_SOURCE_OPEN_STK <= a < spZ regs) ->
    aview SEGS (w_H W) (ms_mem msx) a = aview SEGS (w_H W) memc a);
  [ clear_big; intros a Hqa Hqw;
    rewrite (UN3 a ltac:(alia) ltac:(intros [Hc | Hc]; alia));
    rewrite (UN2 a ltac:(alia)
      ltac:(unfold SB_OP, SHADOW_OFF in *; intros [Hc | [Hc | [Hc | Hc]]]; alia));
    pose proof HK as (K1 & _); rewrite (K1 a ltac:(alia) ltac:(alia));
    apply UN1; [alia | intros Hc; alia]
  |]
  end.
Time lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
  assert (HIMG : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
    ~ (as_errno B <= a < as_errno B + 4) ->
    aview SEGS (w_H W) (ms_mem msx) a = aview SEGS (w_H W) memc a);
  [ clear_big; intros a Hi Ho He; pose proof (pa_img_range a Hi) as Hr1; pose proof (pa_segs_low a Hi) as Hr2;
    destruct Hfimg as [Hfi | Hfi]; destruct HFimg as [HFi | HFi];
    (rewrite (UN3 a ltac:(alia) ltac:(intros [Hc | Hc]; alia));
     rewrite (UN2 a ltac:(alia)
       ltac:(unfold SB_OP, SHADOW_OFF in *; intros [Hc | [Hc | [Hc | Hc]]]; alia));
     pose proof HK as (_ & _ & K3 & _); rewrite (K3 a Hi Ho He);
     apply UN1; [alia | intros Hc; alia])
  |]
  end.
Time lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
  assert (HBLK : forall b0 m0 i, In (b0, m0) (ablocks B lyc Sc) -> 0 <= i < req_size m0 ->
    aview SEGS (w_H W) (ms_mem msx) (b0 + i) = aview SEGS (w_H W) memc (b0 + i));
  [ clear_big; intros b0 m0 i Hb Hi;
    destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b0 m0 HAR Hb) as (_ & Hb4096 & Hbceil & Hbapp & _);
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp;
    pose proof (sep_block_frame SEGS B LAWS lyc Sc W memc mdc b0 m0 cid pos HAR Hb Hin) as Dbf;
    unfold zdisjoint in Dbf; cbn [fst snd] in Dbf;
    pose proof (sep_block_frame SEGS B LAWS lyc S2 W mem2 md2 b0 m0 1 fpos HAR2
      ltac:(rewrite Eab; exact Hb) Hfin2) as DbF;
    unfold zdisjoint in DbF; cbn [fst snd] in DbF; fold F in DbF;
    change (fs_frame_bytes 1) with 128 in DbF;
    destruct Hbapp as [Hba0 [Hba | Hba]]; destruct Dbf as [Hd1 | Hd1]; destruct DbF as [Hd2 | Hd2];
    (rewrite (UN3 (b0 + i) ltac:(alia) ltac:(intros [Hc | Hc]; alia));
     rewrite (UN2 (b0 + i) ltac:(alia)
       ltac:(unfold SB_OP, SHADOW_OFF in *; intros [Hc | [Hc | [Hc | Hc]]]; alia));
     pose proof HK as (_ & K2 & _); rewrite (K2 b0 m0 i Hb Hi ltac:(intros []));
     apply UN1; [alia | intros Hc; alia])
  |]
  end.
(* The two saved words the unwinder reads: ra at sp0' - 8 and the caller's s0 at sp0' - 16 (0x811e8, 0x811ec). *)
assert (E3_1 : ew E3v 1 = getr regs 1) by (rewrite OLD3, OLD2, OLD1 by lia; exact E1).
assert (E8 : ew E 8 = getr regs 8)
  by (rewrite (proj1 HAE 8%nat ltac:(lia)); exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
assert (E3_8 : ew E3v 8 = getr regs 8) by (rewrite OLD3, OLD2, OLD1 by lia; exact E8).
assert (E3_3 : ew E3v 3 = getr regs 3) by (rewrite OLD3, OLD2, OLD1 by lia; exact E3).
assert (E3_4 : ew E3v 4 = getr regs 4) by (rewrite OLD3, OLD2, OLD1 by lia; exact E4).
assert (E11 : ew E 11 = getr regs 11)
  by (rewrite (proj1 HAE 11%nat ltac:(lia)); exact (ew_Ereg_nat regs _ 11 11%bv eq_refl)).
assert (E3_11 : ew E3v 11 = getr regs 11) by (rewrite OLD3, OLD2, OLD1 by lia; exact E11).
assert (Hra64 : 0 <= raZ regs < 2 ^ 64)
  by (unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hbr;
      change (bv_modulus 64) with (2 ^ 64) in Hbr; lia).
assert (Hs064 : 0 <= s0Z regs < 2 ^ 64)
  by (unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hbr;
      change (bv_modulus 64) with (2 ^ 64) in Hbr; lia).
Time lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msx) =>
  let r := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_region_nth_g Ex ssx (restrict (w_H W) msx) 3 r HS ltac:(vm_compute; reflexivity)) as HRst;
  cbn [ms_mem restrict mkst] in HRst end.
pose proof (field_of_region E3v _ 2%nat (spZ regs) _ _ _ _ _ (-8) 8%N (SOff 1 0) (raZ regs) HRst U3sp
  ltac:(cbn; tauto)
  ltac:(unfold raZ; cbn [sv_denot]; rewrite E3_1, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
  ltac:(clear_big; cbn; lia) ltac:(cbn; lia)) as Vra.
pose proof (field_of_region E3v _ 2%nat (spZ regs) _ _ _ _ _ (-16) 8%N (SOff 8 0) (s0Z regs) HRst U3sp
  ltac:(cbn; tauto)
  ltac:(unfold s0Z; cbn [sv_denot]; rewrite E3_8, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
  ltac:(clear_big; cbn; lia) ltac:(cbn; lia)) as Vs0.
change (N.to_nat 8) with 8%nat in Vra, Vs0.
(* The ten callee-saved words the unwinder reads below ra: s0, s1 at sp0' - 16, - 24, then s2 .. s9. *)
assert (E3r : forall (r : nat) (rb : bv 5), (r < 32)%nat -> Z.of_nat r = bv_unsigned rb -> ew E3v r = getr regs rb)
  by (intros r rb Hr Hrb; rewrite OLD3, OLD2, OLD1 by lia; rewrite (proj1 HAE r ltac:(lia));
      exact (ew_Ereg_nat regs _ r rb Hrb)).
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
assert (VSAV : forall j, 0 <= j < 10 ->
  val_mem SEGS (mrestrict (w_H W) (ms_mem msx)) (spZ regs + (-16 - 8 * j)) 8
    (bv_unsigned (getr regs (Z_to_bv 5 (if j <? 2 then 8 + j else 16 + j)))));
[ intros j Hj;
  assert (Hj10 : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/ j = 9)
    by (clear_big; lia);
  destruct Hj10 as [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ] ] ] ] ];
  lazymatch goal with |- val_mem _ _ (spZ regs + ?o) 8 (bv_unsigned (getr regs (Z_to_bv 5 ?z))) =>
    let o' := eval vm_compute in o in change o with o';
    let z' := eval vm_compute in z in change z with z' end;
  match goal with |- val_mem _ _ (spZ regs + ?o) 8 (bv_unsigned (getr regs ?rb)) =>
    let rn := eval vm_compute in (Z.to_nat (bv_unsigned rb)) in
    refine (field_of_region E3v _ 2%nat (spZ regs) _ _ _ _ _ o 8%N (SOff rn 0)
      (bv_unsigned (getr regs rb)) HRst U3sp ltac:(cbn; tauto)
      ltac:(cbn [sv_denot]; rewrite (E3r rn rb ltac:(cbn; lia) ltac:(vm_compute; reflexivity)),
            Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
      ltac:(clear_big; pose proof (bv_unsigned_in_range 64 (getr regs rb)) as Hbb;
            change (bv_modulus 64) with (2 ^ 64) in Hbb; change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia)
      ltac:(cbn; lia))
  end
| ] end.
change (N.to_nat 8) with 8%nat in VSAV.
assert (Hra8 : forall mq, val_mem SEGS (mrestrict (w_H W) mq) (spZ regs + -8) 8 (raZ regs) ->
  rdword (aview SEGS (w_H W) mq) (spZ regs - 8) = Some (raZ regs))
  by (intros mq Hv; replace (spZ regs - 8) with (spZ regs + -8) by lia;
      apply (rdword_of_val_mem SEGS); [exact Hv | lia]).
assert (Hs08 : forall mq, val_mem SEGS (mrestrict (w_H W) mq) (spZ regs + -16) 8 (s0Z regs) ->
  rdword (aview SEGS (w_H W) mq) (spZ regs - 16) = Some (s0Z regs))
  by (intros mq Hv; replace (spZ regs - 16) with (spZ regs + -16) by lia;
      apply (rdword_of_val_mem SEGS); [exact Hv | lia]).
(* The call: pc, the registers the callee reads, and the chain with this frame's record (sp0', ra, s0) on top. *)
rewrite pa_sigma_libreac_fuzz_fopen in HS.
Time pmkst HS.
Time prreg_raw HS (1%bv : bv 5) Q1. prreg_raw HS (2%bv : bv 5) Q2. prreg_raw HS (3%bv : bv 5) Q3.
Time prreg_raw HS (4%bv : bv 5) Q4. prreg_raw HS (8%bv : bv 5) Q8. prreg_raw HS (10%bv : bv 5) Q10.
Time prreg_raw HS (11%bv : bv 5) Q11.
prreg_raw HS (9%bv : bv 5) Qs1. prreg_raw HS (18%bv : bv 5) Qs2. prreg_raw HS (19%bv : bv 5) Qs3.
prreg_raw HS (20%bv : bv 5) Qs4. prreg_raw HS (21%bv : bv 5) Qs5. prreg_raw HS (22%bv : bv 5) Qs6.
prreg_raw HS (23%bv : bv 5) Qs7. prreg_raw HS (25%bv : bv 5) Qs9. prreg_raw HS (26%bv : bv 5) Qs10.
prreg_raw HS (27%bv : bv 5) Qs11.
assert (Hsp8 : spZ regs mod 8 = 0)
  by (clear_big; pose proof (Z_div_mod_eq_full (spZ regs) 16) as Dq; rewrite Hal16, Z.add_0_r in Dq; rewrite Dq;
      replace (16 * (spZ regs / 16)) with ((2 * (spZ regs / 16)) * 8) by lia; apply Z.mod_mul; lia).
assert (HctxS : In (spine ((spZ regs, raZ regs, s0Z regs) :: ch)) CTX) by (cbn [spine map fst snd]; exact Hctx).
Time lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
  assert (Qsp : spZ rg = sp0 + (sp1 - sp0))
    by (clear_big; unfold spZ; rewrite Q2; change (bv_unsigned (sv_denot E3v (SOff 60 0))) with (U E3v (SOff 60 0));
        rewrite (U_atom E3v 60 sp1 E3_60) by lia; lia);
  assert (Qs0 : s0Z rg = spZ regs)
    by (clear_big; unfold s0Z; rewrite Q8; change (bv_unsigned (sv_denot E3v (SOff 2 0))) with (U E3v (SOff 2 0));
        rewrite (U_atom E3v 2 (spZ regs) E3_2) by lia; reflexivity);
  assert (Q1' : getr rg 1 = Z_to_bv 64 (BASE + (symaddr ((Symbols.AsanUbsan.s_pcap_source_open + 0x118) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z)))
    by (rewrite Q1; cbn [sv_denot]; exact (img_env_codeptr E3v HEI3 (symaddr ((Symbols.AsanUbsan.s_pcap_source_open + 0x118) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z)));
  assert (Q3' : getr rg 3 = w64 (as_gp B))
    by (rewrite Q3; cbn [sv_denot]; rewrite E3_3, Z.add_0_r, Z_to_bv_bv_unsigned; exact Hgp);
  assert (Q4' : getr rg 4 = w64 (as_tp B))
    by (rewrite Q4; cbn [sv_denot]; rewrite E3_4, Z.add_0_r, Z_to_bv_bv_unsigned; exact Htp);
  assert (Q10' : getr rg 10 = w64 (VAL (A_OBJ 3)))
    by (rewrite Q10; cbn [sv_denot]; rewrite E3_11, Z.add_0_r, Z_to_bv_bv_unsigned; exact H11);
  assert (Q11' : getr rg 11 = w64 (as_mode K))
    by (clear_big; rewrite Q11; cbn [sv_denot]; change 253%nat with (A_OBJ 12);
        rewrite (img_env_atomP E3v (A_OBJ 12) HEI3 ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia));
        rewrite Z.add_0_r, Z_to_bv_bv_unsigned, HMODE; reflexivity);
  assert (HtopB : ly_top lyc <= 2 ^ 64)
    by (clear_big; pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _); rewrite Etop; lia);
  assert (Hkp : forall a, spZ regs <= a < 2 ^ 64 -> aview SEGS (w_H W) mm a = aview SEGS (w_H W) memc a)
    by (clear_big; intros a Ha; apply HHI; lia);
  assert (Hsp1c : alloc_ceiling <= spZ regs /\ spZ regs < ly_top lyc - 16 /\ sp1 + 16 <= spZ regs)
    by (clear_big; lia);
  pose proof (achain_push lyc (aview SEGS (w_H W) memc) (aview SEGS (w_H W) mm) (spZ regs) (s0Z regs) (raZ regs)
    ch sp1 Hch HtopB Hkp (Hra8 mm Vra) (Hs08 mm Vs0) Hra4 (proj1 Hsp1c) Hsp8 (proj1 (proj2 Hsp1c))
    (proj2 (proj2 Hsp1c))) as Hch1';
  assert (Hch1 : achain lyc (aview SEGS (w_H W) mm) (sp0 + (sp1 - sp0)) (s0Z rg)
                   ((spZ regs, raZ regs, s0Z regs) :: ch))
    by (clear_big; replace (sp0 + (sp1 - sp0)) with sp1 by lia; rewrite Qs0; exact Hch1');
  (* The callee's premises at the call state, from the entry's through the three steps' kept clauses. *)
  assert (HROc : roimg (rdW W mm)) by (apply (ROK W memc mm); [intros a Hi Ho He _; apply HIMG; assumption | exact HRO]);
  assert (HVnc : val_mem SEGS (rdW W mm) (VAL (A_OBJ 4)) 8 n)
    by (apply (vm_frame (rdW W memc)); [|exact HVn]; intros x Hx; apply (mbyte_of_aview SEGS);
        destruct (HGX x ltac:(left; clear_big; lia)) as (Hgi & Hgo & Hge); apply HIMG; assumption);
  assert (HVbc : val_mem SEGS (rdW W mm) (VAL (A_OBJ 2)) 8 b)
    by (apply (vm_frame (rdW W memc)); [|exact HVb]; intros x Hx; apply (mbyte_of_aview SEGS);
        destruct (HGX x ltac:(right; clear_big; lia)) as (Hgi & Hgo & Hge); apply HIMG; assumption);
  assert (HNONEc : asource_none SEGS K (rdW W mm))
    by (apply (asource_none_frame K (rdW W memc)); [|exact HNONE]; intros x Hx; apply (mbyte_of_aview SEGS);
        destruct (asil_env _ _ _ _ ASIL x Hx) as (Hgi & Hgo & Hge); apply HIMG; assumption);
  assert (Hinputc : 1 <= n -> In (b, n) (ablocks B lyc S2) /\ garr8 SEGS (rdW W mm) b C /\ bytes_ok C);
  [ clear_big; intros Hn1; destruct (Hinput Hn1) as (Hinb & Hgb & Hbok);
    pose proof (req_size_pos n ltac:(lia)) as [_ Hreqn];
    split; [rewrite Eab; exact Hinb|]; split; [|exact Hbok];
    apply (garr8_frame SEGS (rdW W memc) _ _ _ Hgb); intros x Hx; apply (mbyte_of_aview SEGS);
    replace x with (b + (x - b)) by lia; apply (HBLK b n (x - b) Hinb); lia
  | ];
  assert (HPA : range_addressable (aview SEGS (w_H W) mm) SHADOW_OFF (VAL (A_OBJ 3)) 13 /\
                shadow_hull_vis (aview SEGS (w_H W) mm) (VAL (A_OBJ 3)) 13)
    by (apply (HPATH lyc S2 W mm mdq); exact (proj1 HJ2)) end.
(* The frame's own words at the call: the header (0x812a4..0x812ac), the flag pointer, the 12 written shadow
   bytes and the unwinder slot *(s1). *)
Time lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msx) =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_region_nth_g Ex ssx (restrict (w_H W) msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HRsl;
  let r1 := eval vm_compute in (nth 1 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_region_nth_g Ex ssx (restrict (w_H W) msx) 1 r1 HS ltac:(vm_compute; reflexivity)) as HRsh;
  let r2 := eval vm_compute in (nth 2 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_region_nth_g Ex ssx (restrict (w_H W) msx) 2 r2 HS ltac:(vm_compute; reflexivity)) as HRfr;
  cbn [ms_mem restrict mkst] in HRsl, HRsh, HRfr end.
assert (HFL64 : 0 <= FL < 2 ^ 64) by (clear_big; destruct HFLrng as (_ & Hq1 & _ & Hq2); lia).
pose proof (field_of_region E3v _ 60%nat sp1 _ _ _ _ _ 0 8%N (SOff 44 0) F HRsl U60 ltac:(cbn; tauto)
  ltac:(cbn [sv_denot]; rewrite E3_44, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
  ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear_big; lia) ltac:(cbn; lia)) as Vslot.
pose proof (field_of_region E3v _ 44%nat F _ _ _ _ _ 0 8%N (SLit 1102416563) OP_MAGIC HRfr U44
  ltac:(cbn; tauto) ltac:(vm_compute; reflexivity)
  ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold OP_MAGIC; lia) ltac:(cbn; lia)) as Vmag.
pose proof (field_of_region E3v _ 44%nat F _ _ _ _ _ 8 8%N (SOff 251 0) (VAL (A_OBJ 10)) HRfr U44
  ltac:(cbn; tauto)
  ltac:(change 251%nat with (A_OBJ 10); cbn [sv_denot];
        rewrite (img_env_atomP E3v (A_OBJ 10) HEI3 ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia));
        rewrite unsigned_lit_small by (pose proof (pa_val_range (A_OBJ 10)); lia); rewrite Z.add_0_r; reflexivity)
  ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear_big; pose proof (pa_val_range (A_OBJ 10)); lia)
  ltac:(cbn; lia)) as Vo10.
pose proof (field_of_region E3v _ 44%nat F _ _ _ _ _ 16 8%N (SOff 252 0) (VAL (A_OBJ 11)) HRfr U44
  ltac:(cbn; tauto)
  ltac:(change 252%nat with (A_OBJ 11); cbn [sv_denot];
        rewrite (img_env_atomP E3v (A_OBJ 11) HEI3 ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia));
        rewrite unsigned_lit_small by (pose proof (pa_val_range (A_OBJ 11)); lia); rewrite Z.add_0_r; reflexivity)
  ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear_big; pose proof (pa_val_range (A_OBJ 11)); lia)
  ltac:(cbn; lia)) as Vo11.
pose proof (field_of_region E3v _ 44%nat F _ _ _ _ _ 120 8%N (SOff 61 0) FL HRfr U44 ltac:(cbn; tauto)
  ltac:(cbn [sv_denot]; rewrite E61, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
  ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear_big; lia) ltac:(cbn; lia)) as Vflag.
change (N.to_nat 8) with 8%nat in Vslot, Vmag, Vo10, Vo11, Vflag.
(* The 12 written shadow bytes: each chunk holds a sign-extended literal, so the byte is its value mod 256
   (field_of_region_any, YC4b.v:151): 0xf1 x4 (left redzone), 0xf8 x3 (the header buffer, out of scope) and
   0xf3 x5 (the right redzone) = OSH_out's first twelve. *)
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
assert (VSH : forall i, 0 <= i < 12 ->
  aview SEGS (w_H W) (ms_mem msx) (SB_OP + F / 8 + i) = Some (nth (Z.to_nat i) OSH_out 0)) end.
{ intros i Hi.
  assert (Hi12 : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9
                 \/ i = 10 \/ i = 11) by (clear_big; lia).
  destruct Hi12 as [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | -> ]]]]]]]]]]];
  lazymatch goal with |- _ = Some ?v => let v' := eval vm_compute in v in change v with v' end;
  (apply (aview_of_val_mem1 SEGS); [|clear_big; lia]);
  lazymatch goal with |- val_mem _ _ (?bb + ?o) 1 ?v =>
    lazymatch type of HRsh with region_ok _ _ _ (YP09.mkRegion _ _ _ _ _ ?cs) =>
      let ch := eval vm_compute in
        (List.find (fun c => Z.eqb (YP09.c_off c) o) cs) in
      lazymatch ch with Some (YP09.mkChunk _ (CVal _ ?ee)) =>
        let V := fresh "Vb" in
        pose proof (field_of_region_any (segs := SEGS) E3v _ 62%nat (SB_OP + F / 8) _ _ _ _ _ o 1%N ee
          HRsh U62 ltac:(cbn; tauto) ltac:(cbn; lia)) as V;
        change (N.to_nat 1) with 1%nat in V;
        let vv := eval vm_compute in (bv_unsigned (sv_denot E3v ee) mod 2 ^ (8 * Z.of_N 1)) in
        change (bv_unsigned (sv_denot E3v ee) mod 2 ^ (8 * Z.of_N 1)) with vv in V;
        exact V end end end. }
(* The last four shadow bytes are still the zeros __asan_stack_malloc_1 left: the stretch's write window is
   [0, 12) of the shadow region, so UN2 and UN3 carry them. *)
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
assert (VSH2 : forall i, 12 <= i < 16 -> aview SEGS (w_H W) (ms_mem msx) (SB_OP + F / 8 + i) = Some 0) end.
{ intros i Hi.
  rewrite (UN3 (SB_OP + F / 8 + i) ltac:(unfold SB_OP in *; alia)
                ltac:(unfold SB_OP in *; intros [Hc | Hc]; alia)).
  rewrite (UN2 (SB_OP + F / 8 + i) ltac:(unfold SB_OP in *; alia)
                ltac:(unfold SB_OP, SHADOW_OFF in *; intros [Hc | [Hc | [Hc | Hc]]]; alia)).
  replace (SB_OP + F / 8 + i) with (SHADOW_OFF + F / 8 + i) by (unfold SB_OP, SHADOW_OFF; lia).
  apply Hz. change (128 / 8) with 16. lia. }

(* ---- the checkpoint, assembled ---- *)
rewrite wvb_collapse in HJ2.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
  assert (HRFP : forall a, F <= a < F + fs_frame_bytes OP_CID -> apresent (w_H W) mm a);
  [ intros a Ha; change (fs_frame_bytes OP_CID) with 128 in Ha;
    destruct (al_frames _ _ LAWS lyc S2 W mm mdq 1 fpos (proj1 HJ2) ltac:(exact Hfin2)) as (_ & _ & HP3 & _);
    change (fs_frame_bytes 1) with 128 in HP3;
    exact (proj1 (HP3 a ltac:(fold F; clear_big; lia)))
  | ];
  assert (UNfrm : forall cid' pos' a, In (cid', pos') (frames Sc) ->
    (in_zr a (frame_rng lyc (cid', pos')) \/
     in_zr a (shadow_addr (frame_addr lyc cid' pos'), fs_frame_bytes cid' / 8)) ->
    aview SEGS (w_H W) mm a = aview SEGS (w_H W) memc a);
  [ intros cid' pos' a Hin' Hr;
    destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid' pos' HAR Hin') as (Hg4096 & Hgceil & Hgapp);
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hgapp;
    destruct (frame_al64 SEGS B lyc Sc W memc mdc cid' pos' HAR Hin') as (Hga64 & Hgb64 & Hgbp);
    assert (Hga8 : frame_addr lyc cid' pos' = 8 * (frame_addr lyc cid' pos' / 8))
      by (apply div8_eq64; exact Hga64);
    assert (Hgb8 : fs_frame_bytes cid' = 8 * (fs_frame_bytes cid' / 8)) by (apply div8_eq64; exact Hgb64);
    assert (Hdg : F + 128 <= frame_addr lyc cid' pos' \/ frame_addr lyc cid' pos' + fs_frame_bytes cid' <= F);
    [ destruct (in_split _ _ Hin') as (l2 & l3 & El);
      pose proof (sep_frames_pos SEGS B LAWS lyc S2 W mem2 md2 (1, fpos) (cid', pos') [] l2 l3 HAR2
        ltac:(rewrite Hfrs2, El; reflexivity)) as Hd;
      unfold zdisjoint, frame_rng in Hd; cbn [fst snd] in Hd; fold F in Hd;
      change (fs_frame_bytes 1) with 128 in Hd; clear_big; lia
    | ];
    unfold frame_rng, in_zr, shadow_addr in Hr; cbn [fst snd] in Hr;
    assert (Ha64 : 0 <= a < 2 ^ 64) by (destruct Hr as [Hr | Hr]; unfold SHADOW_OFF in *; alia);
    assert (Hex3 : ~ (sp1 <= a < sp1 + 8 \/ spZ regs - 88 <= a < spZ regs))
      by (destruct Hr as [Hr | Hr]; unfold SHADOW_OFF in *; intros [Hc | Hc]; alia);
    assert (Hex1 : ~ (spZ regs - 112 <= a < spZ regs))
      by (destruct Hr as [Hr | Hr]; unfold SHADOW_OFF in *; intros Hc; alia);
    assert (Hex2 : ~ (sp1 <= a < sp1 + 8 \/ SB_OP + F / 8 <= a < SB_OP + F / 8 + 12 \/ F <= a < F + 128
                      \/ spZ regs - 88 <= a < spZ regs));
    [ destruct Hr as [Hr | Hr]; destruct Hdg as [Hdg | Hdg]; destruct Hgapp as [Hgap0 [Hgap | Hgap]];
      unfold SB_OP, SHADOW_OFF in *; intros [Hc | [Hc | [Hc | Hc]]]; alia
    | ];
    rewrite (UN3 a Ha64 Hex3); rewrite (UN2 a Ha64 Hex2);
    pose proof HK as (_ & _ & _ & K4 & _);
    rewrite (K4 cid' pos' a Hin' ltac:(unfold frame_rng, in_zr, shadow_addr; cbn [fst snd];
                                       destruct Hr as [Hr | Hr]; [left | right]; clear_big; lia)
                                ltac:(intros []));
    exact (UN1 a Ha64 Hex1)
  | ];
  assert (EXTK : forall a, Exists (in_zr a) (ly_extra lyc) -> ~ (as_errno B <= a < as_errno B + 4) ->
    aview SEGS (w_H W) mm a = aview SEGS (w_H W) memc a);
  [ intros a HX He;
    destruct (AR_extra_law_ok SEGS B lyc Sc W memc mdc a HAR HX) as (_ & _ & _ & Xs & _ & Xsh & Xapp);
    destruct (AR_extra_law_ok SEGS B lyc S2 W mem2 md2 a HAR2 HX) as (_ & _ & Yf & _ & _ & _ & _);
    destruct (Yf 1 fpos Hfin2) as (Yf1 & _); clear Yf;
    fold F in Yf1; change (fs_frame_bytes 1) with 128 in Yf1;
    unfold app_addr, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Xapp;
    pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & Eshi & _);
    rewrite Eslo, Eshi in Xs;
    pose proof HJe as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F5e & _);
    assert (Ha64 : 0 <= a < 2 ^ 64) by (clear - Xapp C1; lia);
    assert (Nstk : forall lo hi, ly_stk_lo ly <= lo -> hi <= ly_stk_hi ly -> ~ (lo <= a < hi))
      by (intros lo hi Hlo Hhi Hc; apply Xs; nlia);
    assert (Nsh : forall lo hi, SHADOW_OFF <= lo -> hi <= kHighShadowEnd -> ~ (lo <= a < hi))
      by (intros lo hi Hlo Hhi Hc; apply Xsh; nlia);
    assert (Hsh1 : SHADOW_OFF <= SB_OP + F / 8 /\ SB_OP + F / 8 + 12 <= kHighShadowEnd)
      by (unfold SB_OP, SHADOW_OFF; rewrite C2; nlia);
    rewrite (UN3 a Ha64 ltac:(intros [Hc | Hc];
      [ exact (Nstk sp1 (sp1 + 8) ltac:(nlia) ltac:(nlia) Hc)
      | exact (Nstk (spZ regs - 88) (spZ regs) ltac:(nlia) ltac:(nlia) Hc) ]));
    rewrite (UN2 a Ha64 ltac:(intros [Hc | [Hc | [Hc | Hc]]];
      [ exact (Nstk sp1 (sp1 + 8) ltac:(nlia) ltac:(nlia) Hc)
      | exact (Nsh (SB_OP + F / 8) (SB_OP + F / 8 + 12) (proj1 Hsh1) (proj2 Hsh1) Hc)
      | exact (Yf1 Hc)
      | exact (Nstk (spZ regs - 88) (spZ regs) ltac:(nlia) ltac:(nlia) Hc) ]));
    rewrite (F5e a HX He);
    apply UN1; [exact Ha64 | intros Hc; exact (Nstk (spZ regs - 112) (spZ regs) ltac:(nlia) ltac:(nlia) Hc)]
  | ];
  assert (PSK : forall i, 0 <= i < 24 -> aview SEGS (w_H W) mm (ps + i) = aview SEGS (w_H W) memc (ps + i));
  [ intros i Hi;
    rewrite (UN3 (ps + i) ltac:(alia) ltac:(intros [Hc | Hc]; alia));
    rewrite (UN2 (ps + i) ltac:(alia)
      ltac:(unfold SB_OP, SHADOW_OFF in *; destruct HdFps as [Hd | Hd]; intros [Hc | [Hc | [Hc | Hc]]]; alia));
    pose proof HK as (_ & _ & _ & K4 & _);
    rewrite (K4 cid pos (ps + i) Hin ltac:(left; unfold frame_rng, in_zr; cbn [fst snd]; clear_big; lia)
      ltac:(intros []));
    apply UN1; [alia | intros Hc; alia]
  | ];
  assert (RAps : range_addressable (aview SEGS (w_H W) mm) SHADOW_OFF ps 24);
  [ apply (ra_frame (aview SEGS (w_H W) mem2)); [exact HRA2|];
    intros x Hx; unfold shadow_of_addr;
    pose proof (shadow_rng_in _ _ x Hfa8 Hfb8 ltac:(clear_big; lia)) as Hrng;
    rewrite (UN3 (SHADOW_OFF + x / 8) ltac:(unfold SHADOW_OFF in *; alia)
      ltac:(unfold SHADOW_OFF in *; intros [Hc | Hc]; alia));
    rewrite (UN2 (SHADOW_OFF + x / 8) ltac:(unfold SHADOW_OFF in *; alia)
      ltac:(unfold SB_OP, SHADOW_OFF in *; destruct HdFps as [Hd | Hd];
            intros [Hc | [Hc | [Hc | Hc]]]; alia));
    reflexivity
  | ];
  assert (HFDS0 : m_fds mdq = m_fds mdc /\ m_fs mdq = m_fs mdc);
  [ pose proof HJe as (_ & _ & _ & _ & Haos0 & _);
    destruct (aos_step_closed [] _ _ ltac:(intros (r & [] & _)) Haos0) as (Hfd2 & Hfsys2 & _ & _);
    destruct (sbm_fds _ _ (same_but_materialized_wvb_any md2 mat1)) as (Ef1 & Eg1);
    destruct (sbm_fds _ _ (same_but_materialized_wvb_any mdc mat)) as (Ef0 & Eg0);
    split;
    [ rewrite Ef1; unfold m_fds; rewrite Hfd2; unfold m_fds in Ef0; rewrite Ef0; reflexivity
    | rewrite Eg1; unfold m_fs; rewrite Hfsys2; unfold m_fs in Eg0; rewrite Eg0; reflexivity ]
  | ];
  apply SRr_ret; split; [reflexivity|];
  exists fpos, F, FL, sp1, S2, rg, mm, mdq;
  split; [reflexivity|];
  cbn [o_STK o_sp0 o_FP o_ly o_S o_W0 o_mem0 o_md0 o_own o_lyc o_Sc o_W o_memc o_mdc o_k o_regs o_ch o_ps
       o_n o_b o_M o_C o_cid o_pos];
  unfold op_at_call, oF, oFL, osp1;
  cbn [o_STK o_sp0 o_FP o_ly o_S o_W0 o_mem0 o_md0 o_own o_lyc o_Sc o_W o_memc o_mdc o_k o_regs o_ch o_ps
       o_n o_b o_M o_C o_cid o_pos];
  change OP_CID with 1;
  split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
  split; [exact HJ2|]; split; [exact Hfrs2|]; split; [exact Hnin|]; split; [exact Hnev2|];
  split; [exact Hbb2|]; split; [exact Eab|]; split; [exists fS2; exact ES2|];
  split; [rewrite Qsp; clear_big; lia|];
  split; [exact Qs0|];
  split; [exact Q1'|];
  split; [rewrite Q3; cbn [sv_denot]; rewrite E3_3, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity|];
  split; [rewrite Q4; cbn [sv_denot]; rewrite E3_4, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity|];
  split; [rewrite Qs1; cbn [sv_denot]; rewrite E3_60; unfold w64;
          rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity|];
  split; [exact Q10'|]; split; [exact Q11'|];
  split; [rewrite Qs2; cbn [sv_denot]; rewrite E3_44; unfold w64;
          rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity|];
  split; [rewrite Qs3; cbn [sv_denot]; rewrite E3_10; unfold w64;
          rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity|];
  split; [rewrite Qs4; cbn [sv_denot]; rewrite E3_11, H11; unfold w64;
          rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity|];
  split; [rewrite Qs5; cbn [sv_denot]; rewrite E62; unfold w64;
          rewrite Z.add_0_r, Z_to_bv_bv_unsigned; f_equal; unfold SB_OP, SHADOW_OFF; lia|];
  split; [rewrite Qs6; cbn [sv_denot]; rewrite E3_44; unfold w64;
          rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity|];
  split; [rewrite Qs7; cbn [sv_denot]; rewrite E3_32; unfold w64;
          rewrite Z.add_0_r, Z_to_bv_bv_unsigned; f_equal; unfold SB_OP, SHADOW_OFF; lia|];
  split; [rewrite Qs9; cbn [sv_denot];
          rewrite (E3r 25%nat 25%bv ltac:(clear_big; lia) ltac:(vm_compute; reflexivity));
          rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity|];
  split; [rewrite Qs10; cbn [sv_denot];
          rewrite (E3r 26%nat 26%bv ltac:(clear_big; lia) ltac:(vm_compute; reflexivity));
          rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity|];
  split; [rewrite Qs11; cbn [sv_denot];
          rewrite (E3r 27%nat 27%bv ltac:(clear_big; lia) ltac:(vm_compute; reflexivity));
          rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity|];
  split; [exact (Hra8 mm Vra)|];
  split; [ intros j Hj; replace (spZ regs - 16 - 8 * j) with (spZ regs + (-16 - 8 * j)) by (clear_big; lia);
           apply (rdword_of_val_mem SEGS); [exact (VSAV j Hj)|];
           clear_big; pose proof (bv_unsigned_in_range 64
             (getr regs (Z_to_bv 5 (if j <? 2 then 8 + j else 16 + j))));
           change (bv_modulus 64) with (2 ^ 64) in *; lia |];
  split; [ apply (rdword_of_val_mem SEGS);
           [ replace F with (F + 0) at 1 by (clear_big; lia); exact Vmag | unfold OP_MAGIC; clear_big; lia ] |];
  split; [ apply (rdword_of_val_mem SEGS);
           [ exact Vo10 | clear_big; pose proof (pa_val_range (A_OBJ 10)); lia ] |];
  split; [ apply (rdword_of_val_mem SEGS);
           [ exact Vo11 | clear_big; pose proof (pa_val_range (A_OBJ 11)); lia ] |];
  split; [ apply (rdword_of_val_mem SEGS);
           [ change OP_FLAGPTR with 120; exact Vflag | clear_big; lia ] |];
  split; [ intros i Hi;
           replace (SHADOW_OFF + F / 8 + Z.of_nat i) with (SB_OP + F / 8 + Z.of_nat i)
             by (unfold SB_OP, SHADOW_OFF; lia);
           destruct (Z_lt_le_dec (Z.of_nat i) 12) as [Hlt | Hge];
           [ rewrite (VSH (Z.of_nat i) ltac:(clear_big; lia)); rewrite Nat2Z.id; reflexivity
           | rewrite (VSH2 (Z.of_nat i) ltac:(clear_big; lia));
             assert (Hi4 : i = 12%nat \/ i = 13%nat \/ i = 14%nat \/ i = 15%nat) by (clear_big; lia);
             destruct Hi4 as [ -> | [ -> | [ -> | -> ] ] ]; reflexivity ] |];
  split; [ replace sp1 with (sp1 + 0) at 1 by (clear_big; lia);
           apply (rdword_of_val_mem SEGS); [exact Vslot | clear_big; lia] |];
  split; [exact HRFP|];
  split; [exact HHI|]; split; [exact HIMG|]; split; [exact HBLK|]; split; [exact UNfrm|];
  split; [exact EXTK|]; split; [exact PSK|]; split; [exact RAps|];
  split; [exact (proj1 HFDS0)|]; split; [exact (proj2 HFDS0)|];
  split; [exact HF4096|];
  split; [change (fs_frame_bytes OP_CID) with 128; exact HFceil|];
  split; [exact HFa64|];
  split; [change (fs_frame_bytes OP_CID) with 128; exact HdFps|];
  split; [exact Hsp1_lo|]; split; [clear_big; lia|]; split; [clear_big; lia|]; split; [exact Hsp1al16|];
  split; [exact Hch1'|];
  split; [exact HROc|]; split; [exact (proj1 HPA)|]; split; [exact (proj2 HPA)|];
  split; [exact HVnc|]; split; [exact HVbc|]; split; [exact HNONEc|]; split; [exact Hinputc|];
  split; [rewrite ES2; apply (mo_ok_set_fs MT MLAWF); exact MOK|];
  split; [clear - Hev Hnev2; rewrite Hnev2; unfold EV_OPEN, EV_FUZZ_FOPEN in *; lia|];
  rewrite Hbb2; exact Hlive
end.
Qed.


Lemma head_to_fopen :
  forall cx, op_pre SK B K MT FM_RA CTX roimg cx ->
  SRr SEGS (o_W cx) (cfg_at SEGS (BASE + AF_pcap_source_open) (o_regs cx) (o_memc cx) (o_mdc cx))
    (fun W2 c2 => exists fpos h ly2 S2 ms md, c2 = mkCfg ms md /\
       op_fopen_ret SK B K MT cx fpos h ly2 S2 W2 ms md).
Proof.
intros cx Hpre. pose proof Hpre as HPRE0.
destruct cx as [STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch ps n b M C cid pos].
unfold op_pre in Hpre. cbn [o_STK o_sp0 o_FP o_ly o_S o_W0 o_mem0 o_md0 o_own o_lyc o_Sc o_W o_memc o_mdc o_k
  o_regs o_ch o_ps o_n o_b o_M o_C o_cid o_pos] in Hpre.
destruct Hpre as (HJ & HROD & Hraw & Hra4 & Hgp & Htp & H10 & H11 & Hch & Hctx & Hal16 & Hwlo & Hwhi & Htop32 & Hnfr
  & Hown & Hfa1 & Hfa2 & Hps0 & Hps8 & Hsh & HFP0 & HRO & HPra & HPhull & HVn & HVb & Hb64 & HNONE & Hn & HnC
  & Hinput & HMETA & Hev & Hlive & MOK & HU0 & HUC).
pose proof pa_B_ok as HBASE. pose proof (pa_base_lo (PL := PL_pcap) (PI := PI)) as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & Hnev & Hk0 & _ & _ & _ & _ & Hgone & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (HTS : TPCAP_SOURCE_OPEN_STK = 18736) by reflexivity.
assert (HFS : LIBREAC_FUZZ_FOPEN_STK = 18624) by reflexivity.
assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hf4096 & Hfceil & Hfapp).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hfapp.
destruct (frame_al64 SEGS B lyc Sc W memc mdc cid pos HAR Hin) as (Hfa64 & Hfb64 & Hfb).
assert (Hfa8 : frame_addr lyc cid pos = 8 * (frame_addr lyc cid pos / 8)) by (apply div8_eq64; exact Hfa64).
assert (Hfb8 : fs_frame_bytes cid = 8 * (fs_frame_bytes cid / 8)) by (apply div8_eq64; exact Hfb64).
(* ---- the walk up to the call: PcapSourceOpen.v's op_to_call ---- *)
eapply SRr_bind; [ eapply op_to_call; eassumption |].
cbv beta. intros W' c' _ (-> & fpos & F & FL & sp1 & S2 & regsc & memc2 & md & -> & HAC).
unfold op_at_call in HAC.
cbn [o_STK o_sp0 o_FP o_ly o_S o_W0 o_mem0 o_md0 o_own o_lyc o_Sc o_W o_memc o_mdc o_k o_regs o_ch o_ps
     o_n o_b o_M o_C o_cid o_pos] in HAC.
destruct HAC as (HFdef & HFLdef & Hsp1def & HJ2 & Hfrs2 & Hnin & Hnev2 & Hbb2 & Eab & (fS2 & ES2)
  & Qsp & Qs0 & Q1' & Q3' & Q4' & Qs1 & Q10' & Q11' & Qs2 & Qs3 & Qs4 & Qs5 & Qs6 & Qs7 & Qs9 & Qs10 & Qs11
  & Vra2 & VSAV2 & Vmag2 & Vo102 & Vo112 & Vflag2 & VSH2' & Vslot2 & HFpres2
  & HHI & HIMG & HBLK & UNfrm & EXTK & PSK & RAps & Hfds2 & Hfs2
  & HF4096 & HFceil & HFa64 & HdFps & Hsp1_lo & Hsp1_hi & Hsp1r & Hsp1al16
  & Hch1 & HROc & HRApath & HHullpath & HVnc & HVbc & HNONEc & Hinputc & MOK2 & Hev2 & Hlive2).
change (fs_frame_bytes OP_CID) with 128 in HFceil, HdFps, HFpres2.
assert (HAR2 : AR SEGS B lyc S2 W memc2 md) by exact (proj1 HJ2).
assert (Hfin2 : In (OP_CID, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
assert (HinS2 : In (cid, pos) (frames S2)) by (rewrite Hfrs2; right; exact Hin).
assert (HF8eq : F = 8 * (F / 8)) by (apply div8_eq64; exact HFa64).
assert (HF8b : 0 <= F / 8 <= 2 ^ 44) by (clear_big; split; [|]; nlia).
(* ---- the call of libreac_fuzz_fopen (0x812f4) ---- *)

(* the journal at the call is already stated at the call's own model *)
Time eapply SRr_bind;
[ eapply (cl_callS B LAWS W regsc memc2 _ STK sp0 FP ly S W0 mem0 md0 ((OP_CID, fpos) :: own) lyc S2 md k
    LIBREAC_FUZZ_FOPEN_STK afmemopen_fp EV_FUZZ_FOPEN (sp1 - sp0) (w64 (BASE + OP_RET_FOPEN))
    ((spZ regs, raZ regs, s0Z regs) :: ch)
    (fun ly3 S3 W3 regs3 mem3 md3 => exists h : Z,
       getr regs3 10 = w64 h /\ frames S3 = frames S2 /\
       m_fds md3 = m_fds md /\ m_fs md3 = m_fs md /\
       (n = 0 -> h = 0 /\ ablocks B ly3 S3 = ablocks B lyc S2 /\ asource_none SEGS K (rdW W3 mem3) /\
          mo_le MT S2 S3 0) /\
       (1 <= n -> 4096 <= h /\ h mod 16 = 0 /\ ablocks B ly3 S3 = ablocks B lyc S2 ++ [(h, SRC_FILE_BLOCK)] /\
          asource_unbuffered SEGS K (rdW W3 mem3) h b C 0 /\ mo_le MT S2 S3 (mo_malloc MT SRC_FILE_BLOCK)))
    HJ2 ltac:(rewrite Qsp; clear_big; lia));
  [ clear_big; rewrite Zminus_mod, Hsp1al16, Hsp0al; reflexivity
  | clear_big; lia
  | clear_big; vm_compute; discriminate
  | clear_big; lia
  | rewrite Q3'; exact Hgp | rewrite Q4'; exact Htp | exact Q1'
  | apply ret_ok_codeptr_v; [clear_big; unfold OP_RET_FOPEN; lia | reflexivity]
  | unfold w64, OP_RET_FOPEN; rewrite unsigned_lit_small by (clear_big; lia); clear_big; lia
  | replace (sp0 + (sp1 - sp0)) with sp1 by (clear_big; lia); rewrite Qs0; exact Hch1
  | (* the callee *)
    intros HPRE1; eapply SRr_mono;
    [ refine (FOPEN lyc S2 W regsc memc2 md ((spZ regs, raZ regs, s0Z regs) :: ch) n b C HPRE1
        ltac:(cbn [spine map fst snd]; exact Hctx) Q10' Q11' HROc HRApath HHullpath HVnc HVbc Hb64 HNONEc
        Hn HnC Hinputc Hev2 Hlive2 MOK2 HU0 HUC)
    | cbv beta; intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ1 & HP & HQ);
      exists ly3, S3, regs3, mem3, md3; split; [rewrite Q1'; reflexivity|];
      split; [exact HJ1|]; split; [exact HP | exact HQ] ]
  | intros a Ha; left; apply in_fp_inFP in Ha; destruct Ha as (r & [<- | []] & Hr); cbn in Hr;
    replace a with 0 by (clear_big; lia); exact HFP0 ]
|].

(* ---- at the return 0x812f8: what op_fopen_ret states ---- *)
cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJo & HJf & HPo &
  (h & Hh10 & Hfrs3 & Hfds3 & Hfs3 & HQn & HQp)).
replace (sp0 + (sp1 - sp0)) with sp1 in HJf by (clear_big; lia).
pose proof HJf as (HAR3 & Hly3 & _ & _ & _ & _ & Hnev3 & _ & G1 & G2 & G3 & G4 & _ & Gpres & _).
pose proof Hly3 as (_ & _ & _ & _ & _ & EF3 & _ & _ & Etop3 & _).
pose proof Hly3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eextra3 & _).
(* what the call kept of this walk's own bytes *)
assert (TRS : forall a, (spZ regs - 88 <= a < spZ regs) \/ (sp1 <= a < sp1 + 8) ->
  aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W) memc2 a)
  by (intros a Ha; apply G1; clear_big; destruct Ha; lia).
assert (TRF : forall a, (F <= a < F + 128) \/ (SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 16) ->
  aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W) memc2 a).
{ intros a Ha. apply (G4 OP_CID fpos a ltac:(rewrite Hfrs2; left; reflexivity)).
  - rewrite HFdef in Ha. unfold oF in Ha. cbn [o_lyc] in Ha.
    destruct Ha as [Ha | Ha]; [left | right]; unfold frame_rng, in_zr, shadow_addr; cbn [fst snd];
    change (fs_frame_bytes OP_CID / 8) with 16; change (fs_frame_bytes OP_CID) with 128;
    unfold SHADOW_OFF in *; clear_big; lia.
  - intros Hf. apply in_fp_inFP in Hf. destruct Hf as (r & [<- | []] & Hr). cbn in Hr.
    unfold SHADOW_OFF in *. clear_big. destruct Ha; lia. }
assert (TRps : forall i, 0 <= i < 24 ->
  aview SEGS (w_H W3) mem3 (ps + i) = aview SEGS (w_H W) memc2 (ps + i)).
{ intros i Hi. apply (G4 cid pos (ps + i) HinS2).
  - left. unfold frame_rng, in_zr. cbn [fst snd]. clear_big. lia.
  - intros Hf. apply in_fp_inFP in Hf. destruct Hf as (r & [<- | []] & Hr). cbn in Hr. clear_big. lia. }
(* the frame's bytes are present at the return state *)
assert (HFpres3 : forall a, F <= a < F + fs_frame_bytes OP_CID -> apresent (w_H W3) mem3 a).
{ intros a Ha. change (fs_frame_bytes OP_CID) with 128 in Ha.
  destruct (al_frames _ _ LAWS ly3 S3 W3 mem3 md3 OP_CID fpos HAR3
    ltac:(rewrite Hfrs3, Hfrs2; left; reflexivity)) as (_ & _ & HP3 & _).
  unfold frame_addr in HP3. rewrite EF3 in HP3. change (fs_frame_bytes OP_CID) with 128 in HP3.
  rewrite HFdef in Ha. unfold oF, frame_addr in Ha. cbn [o_lyc] in Ha.
  exact (proj1 (HP3 a ltac:(clear_big; lia))). }
(* ps is still addressable *)
assert (RA3 : range_addressable (aview SEGS (w_H W3) mem3) SHADOW_OFF ps 24).
{ apply (ra_frame (aview SEGS (w_H W) memc2)); [exact RAps|].
  intros x Hx. unfold shadow_of_addr.
  pose proof (shadow_rng_in _ _ x Hfa8 Hfb8 ltac:(clear_big; lia)) as Hrng.
  apply (G4 cid pos (SHADOW_OFF + x / 8) HinS2).
  - right. unfold in_zr, shadow_addr. cbn [fst snd]. clear_big. lia.
  - intros Hf. apply in_fp_inFP in Hf. destruct Hf as (r & [<- | []] & Hr). cbn in Hr.
    unfold SHADOW_OFF in *. clear_big. lia. }
(* what the caller keeps, as topen_kept *)
assert (Hb13 : forall b0 m0, In (b0, m0) (ablocks B lyc Sc) -> In (b0, m0) (ablocks B ly3 S3)).
{ intros b0 m0 Hb. destruct (Z.eq_dec n 0) as [Hn0 | Hn0].
  - destruct (HQn Hn0) as (_ & Eb & _ & _). rewrite Eb, Eab. exact Hb.
  - destruct (HQp ltac:(clear_big; lia)) as (_ & _ & Eb & _ & _). rewrite Eb, Eab.
    apply in_or_app. left. exact Hb. }
assert (HKEPT : topen_kept SK SEGS B lyc Sc W memc W3 mem3
  (spZ regs - TPCAP_SOURCE_OPEN_STK) (spZ regs) (fun _ => False)).
{ apply (topen_kept_call lyc Sc W memc mdc S2 memc2 md ly3 S3 W3 mem3 md3 (spZ regs) sp1 fpos
    HAR Hfrs2 ltac:(intros b0 m0 Hb; rewrite Eab; exact Hb) Hb13 HHI HIMG HBLK UNfrm HJf);
  [| clear_big; lia | clear_big; lia | clear_big; lia].
  pose proof HJo as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3 & _).
  intros a Ha. apply Hpres3. clear_big. lia. }
(* the read-only image and the meta region *)
assert (HROD3 : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W3) mem3)).
{ intros a Hro Ho He.
  assert (Hi : in_img SEGS a)
    by (destruct Hro as [(s & Hs & _ & Hr) | Hgot];
        [exists s; split; [exact Hs | exact Hr] | exact (pa_relro_img a Hgot)]).
  rewrite (G3 a Hi Ho He ltac:(apply fp_spares_below; exact (ro_below_ofl_at a Hro))).
  rewrite (HIMG a Hi Ho He). exact (HROD a Hro Ho He). }
assert (HMETA3 : asrc_meta_inv SEGS K ly3 (rdW W3 mem3) M).
{ destruct HMETA as (HX & Himg & Hp & Hm & Hm0 & Hm47 & Hal & HZ).
  pose proof HJf as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F5f & _).
  split; [rewrite Eextra3; exact HX|]. split; [exact Himg|].
  split; [exact (asrc_meta_ptr_of_AR SK SEGS B K ASIL _ _ _ _ _ HAR3)|].
  split.
  - eapply vm_frame; [|exact Hm]. intros x Hx. cbn in Hx. apply (mbyte_of_aview SEGS).
    destruct (asil_meta _ _ _ _ ASIL x ltac:(clear_big; lia)) as (Hi & Hns & Hee & Hlt).
    rewrite (G3 x Hi Hns Hee ltac:(apply fp_spares_below; exact Hlt)). apply HIMG; assumption.
  - split; [exact Hm0|]. split; [exact Hm47|]. split; [exact Hal|].
    intros a Ha. rewrite <- (HZ a Ha). apply (mbyte_of_aview SEGS).
    assert (HXM : Exists (in_zr a) (ly_extra lyc))
      by (apply Exists_exists; exists (M, AMETA_SIZE);
          split; [exact HX | unfold in_zr; cbn [fst snd]; clear_big; lia]).
    assert (Hne : ~ (as_errno B <= a < as_errno B + 4)).
    { intros He. pose proof (asil_errno_img _ _ _ _ ASIL a He) as Hi.
      destruct (AR_extra_law_ok SEGS B lyc Sc W memc mdc a HAR HXM) as (_ & _ & _ & _ & Hni & _).
      exact (Hni Hi). }
    rewrite (F5f a HXM Hne). exact (EXTK a HXM Hne). }
(* the chain at the return state *)
assert (Hchain3 : achain ly3 (aview SEGS (w_H W3) mem3) sp1 (spZ regs)
  ((spZ regs, raZ regs, s0Z regs) :: ch)).
{ pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etopc & _).
  apply (achain_ly_top lyc ly3); [exact Etop3|].
  apply (achain_kept lyc (aview SEGS (w_H W) memc2) _ sp1 (spZ regs) _ sp1);
  [ exact Hch1 | clear_big; lia | rewrite Etopc; clear_big; lia |].
  intros a Ha. apply G1; clear_big; lia. }
(* ---- op_fopen_ret ---- *)
apply SRr_ret.
exists fpos, h, ly3, S3, (mkst regs3 (w64 (BASE + OP_RET_FOPEN)) mem3 (seg_rom SEGS)), md3.
split; [reflexivity|].
unfold op_fopen_ret.
cbn [o_STK o_sp0 o_FP o_ly o_S o_W0 o_mem0 o_md0 o_own o_lyc o_Sc o_W o_memc o_mdc o_k o_regs o_ch o_ps
     o_n o_b o_M o_C o_cid o_pos ms_regs ms_mem mkst].
unfold oSH. rewrite <- HFdef, <- HFLdef, <- Hsp1def.
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [reflexivity|]. split; [reflexivity|].
split; [exact HJo|].
split; [rewrite Hfrs3; exact Hfrs2|].
split; [exact Hnin|].
split; [clear_big; lia|].
split; [exists (st_fs S3); destruct S3; reflexivity|].
(* the registers: aregs_preserved plus the values at the call *)
split; [ transitivity (getr regsc 2); [exact (HPo 2 ltac:(left; reflexivity))|];
         unfold w64; rewrite <- Qsp; unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity |].
split; [ transitivity (getr regsc 9);
         [exact (HPo 9 ltac:(right; right; right; right; left; reflexivity)) | exact Qs1] |].
split; [ transitivity (getr regsc 8); [exact (HPo 8 ltac:(right; right; right; left; reflexivity))|];
         unfold w64; rewrite <- Qs0; unfold s0Z; rewrite Z_to_bv_bv_unsigned; reflexivity |].
split; [ transitivity (getr regsc 18);
         [exact (HPo 18 ltac:(right; right; right; right; right; clear_big; lia)) | exact Qs2] |].
split; [ transitivity (getr regsc 22);
         [exact (HPo 22 ltac:(right; right; right; right; right; clear_big; lia)) | exact Qs6] |].
split; [ transitivity (getr regsc 19);
         [exact (HPo 19 ltac:(right; right; right; right; right; clear_big; lia)) | exact Qs3] |].
split; [ transitivity (getr regsc 20);
         [exact (HPo 20 ltac:(right; right; right; right; right; clear_big; lia)) | exact Qs4] |].
split; [ transitivity (getr regsc 21);
         [exact (HPo 21 ltac:(right; right; right; right; right; clear_big; lia)) | exact Qs5] |].
split; [ transitivity (getr regsc 23);
         [exact (HPo 23 ltac:(right; right; right; right; right; clear_big; lia)) | exact Qs7] |].
split; [exact Hh10|].
split; [ transitivity (getr regsc 3); [exact (HPo 3 ltac:(right; left; reflexivity)) | exact Q3'] |].
split; [ transitivity (getr regsc 4); [exact (HPo 4 ltac:(right; right; left; reflexivity)) | exact Q4'] |].
split; [ transitivity (getr regsc 25);
         [exact (HPo 25 ltac:(right; right; right; right; right; clear_big; lia)) | exact Qs9] |].
split; [ transitivity (getr regsc 26);
         [exact (HPo 26 ltac:(right; right; right; right; right; clear_big; lia)) | exact Qs10] |].
split; [ transitivity (getr regsc 27);
         [exact (HPo 27 ltac:(right; right; right; right; right; clear_big; lia)) | exact Qs11] |].
(* the machine frame *)
split; [ rewrite (rdword_ext (aview SEGS (w_H W) memc2) (aview SEGS (w_H W3) mem3) (spZ regs - 8)
           ltac:(intros kk Hk; apply TRS; left; clear_big; lia)); exact Vra2 |].
split; [ intros j Hj;
         rewrite (rdword_ext (aview SEGS (w_H W) memc2) (aview SEGS (w_H W3) mem3)
           (spZ regs - 16 - 8 * j) ltac:(intros kk Hk; apply TRS; left; clear_big; lia));
         exact (VSAV2 j Hj) |].
(* the frame's header, its flag pointer, its shadow and the unwinder slot *)
split; [ rewrite (rdword_ext (aview SEGS (w_H W) memc2) (aview SEGS (w_H W3) mem3) F
           ltac:(intros kk Hk; apply TRF; left; clear_big; lia)); exact Vmag2 |].
split; [ rewrite (rdword_ext (aview SEGS (w_H W) memc2) (aview SEGS (w_H W3) mem3) (F + 8)
           ltac:(intros kk Hk; apply TRF; left; clear_big; lia)); exact Vo102 |].
split; [ rewrite (rdword_ext (aview SEGS (w_H W) memc2) (aview SEGS (w_H W3) mem3) (F + 16)
           ltac:(intros kk Hk; apply TRF; left; clear_big; lia)); exact Vo112 |].
split; [ rewrite (rdword_ext (aview SEGS (w_H W) memc2) (aview SEGS (w_H W3) mem3) (F + OP_FLAGPTR)
           ltac:(intros kk Hk; apply TRF; left; change OP_FLAGPTR with 120; clear_big; lia));
         exact Vflag2 |].
split; [ intros i Hi; rewrite (TRF (SHADOW_OFF + F / 8 + Z.of_nat i) ltac:(right; clear_big; lia));
         exact (VSH2' i Hi) |].
split; [ rewrite (rdword_ext (aview SEGS (w_H W) memc2) (aview SEGS (w_H W3) mem3) sp1
           ltac:(intros kk Hk; apply TRS; right; clear_big; lia)); exact Vslot2 |].
split; [exact HFpres3|].
(* ps, kept and addressable *)
split; [ intros i Hi; rewrite (TRps i Hi); exact (PSK i Hi) |].
split; [exact RA3|].
split; [exact HKEPT|].
split; [exact HROD3|].
split; [exact HMETA3|].
split; [rewrite Hfds3; exact Hfds2|].
split; [rewrite Hfs3; exact Hfs2|].
split; [exact Hchain3|].
split.
- intros Hn0. destruct (HQn Hn0) as (Hh0 & Eb & Hnone & Hmo). split; [exact Hh0|].
  split; [rewrite Eb; exact Eab|]. split; [exact Hnone|].
  rewrite ES2 in Hmo. exact (mo_le_set_fs_l MT MLAWF Sc S3 fS2 0 Hmo).
- intros Hn1. destruct (HQp Hn1) as (Hh4 & Hh16 & Eb & Hsrc & Hmo).
  split; [exact Hh4|]. split; [exact Hh16|]. split; [rewrite Eb, Eab; reflexivity|].
  split; [exact Hsrc|].
  split; [rewrite ES2 in Hmo; exact (mo_le_set_fs_l MT MLAWF Sc S3 fS2 _ Hmo)|].
  (* fclose's footprint: the sink token is the caller's, the FILE block is this call's *)
  intros x Hx. apply in_fp_inFP in Hx. destruct Hx as (r & [<- | [<- | []]] & Hr); cbn in Hr.
  + change SRC_FILE_BLOCK with 1304 in Hr.
    destruct (in_dec zz_eq_dec (h, SRC_FILE_BLOCK) (ablocks B lyc Sc)) as [Hdup | Hnew].
    * exfalso. destruct (in_split _ _ Hdup) as (l1 & l2 & El).
      pose proof (sep_blocks_pos SEGS B LAWS ly3 S3 W3 mem3 md3 (h, SRC_FILE_BLOCK) (h, SRC_FILE_BLOCK)
        l1 l2 [] HAR3 ltac:(rewrite Eb, Eab, El; rewrite <- app_assoc; reflexivity)) as Hd.
      unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd.
      change (req_size SRC_FILE_BLOCK) with 1304 in Hd. clear_big. lia.
    * destruct (in_dec zz_eq_dec (h, SRC_FILE_BLOCK) (ablocks B ly S)) as [Hold | Hfresh].
      -- left. replace x with (h + (x - h)) by (clear_big; lia).
         apply (Hgone h SRC_FILE_BLOCK (x - h) Hold Hnew).
         change (req_size SRC_FILE_BLOCK) with 1304. clear_big. lia.
      -- right. exists h, SRC_FILE_BLOCK.
         split; [rewrite Eb, Eab; apply in_or_app; right; left; reflexivity|].
         split; [exact Hfresh|]. change (req_size SRC_FILE_BLOCK) with 1304. clear_big. lia.
  + left. replace x with 0 by (clear_big; lia). exact HFP0.
Qed.

(* ---- the contract ---------------------------------------------------------------------------- *)

(* The whole walk, from the two cuts of PcapSourceOpenPh.v: the head (here), the middle
   (PcapSourceOpenPhM.v, op_from_fopen) and the tail (PcapSourceOpenB.v, op_from_null / op_from_read). *)
Theorem pb_pcap_source_openX_of :
  op_from SK B K MT FM_RA CTX roimg (op_gi_null SK B K MT) ->
  op_from SK B K MT FM_RA CTX roimg (op_gi_read SK B K MT) ->
  op_from_fopen_stmt SK B K MT FM_RA CTX roimg ->
  tpcap_source_open_specX SK SEGS pa_relro_lo pa_relro_hi (VAL (A_OBJ 3)) (VAL (A_OBJ 4)) (VAL (A_OBJ 2)) roimg
    B K MT FM_RA CTX (BASE + AF_pcap_source_open).
Proof.
intros OFN OFR HMID. unfold tpcap_source_open_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch ps n b M C cid pos.
intros H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30
  H31 H32 H33 H34 H35 H36 H37 H38.
set (cx := mkOCX STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch ps n b M C cid pos).
assert (HPRE : op_pre SK B K MT FM_RA CTX roimg cx).
{ unfold op_pre, cx. cbn [o_STK o_sp0 o_FP o_ly o_S o_W0 o_mem0 o_md0 o_own o_lyc o_Sc o_W o_memc o_mdc o_k
    o_regs o_ch o_ps o_n o_b o_M o_C o_cid o_pos].
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj H10 (conj H11
    (conj H12 (conj H13 (conj H14 (conj H15 (conj H16 (conj H17 (conj H18 (conj H19 (conj H20 (conj H21
    (conj H22 (conj H23 (conj H24 (conj H25 (conj H26 (conj H27 (conj H28 (conj H29 (conj H30 (conj H31
    (conj H32 (conj H33 (conj H34 (conj H35 (conj H36 (conj H37 H38))))))))))))))))))))))))))))))))))))). }
eapply SRr_bind; [ exact (head_to_fopen cx HPRE) |].
cbv beta. intros W2 c2 _ (fpos & h & ly2 & S2 & ms & md & -> & HFR).
exact (HMID cx fpos h ly2 S2 W2 ms md HPRE HFR).
Qed.

(* The closed contract: the head here, the middle (PcapSourceOpenPhM.v) and the tail (PcapSourceOpenB.v). *)
Theorem pb_pcap_source_openX :
  tpcap_source_open_specX SK SEGS pa_relro_lo pa_relro_hi (VAL (A_OBJ 3)) (VAL (A_OBJ 4)) (VAL (A_OBJ 2)) roimg
    B K MT FM_RA CTX (BASE + AF_pcap_source_open).
Proof.
pose proof (op_from_null SK B K MT FM_RA CTX roimg LAWS ML ASF FFL MLAW MLAWF ASIL) as ONULL.
pose proof (op_from_read SK B K MT FM_RA CTX roimg LAWS ML ASF FFL MLAW MLAWF FM ra_fc1 ra_fc2 AFCLOSE
  HUfc1 HUfc2 ASIL) as OREAD.
exact (pb_pcap_source_openX_of ONULL OREAD
  (op_from_fopen SK B K MT FM_RA CTX roimg LAWS ASIL AFREAD ONULL OREAD)).
Qed.

End e.
End d.
End b.

(* SK stays explicit on every exported name (a Theorem Labs lane ruling 21:57Z). *)
Arguments head_to_fopen {fx rc} SK {PI}.
Arguments pb_pcap_source_openX_of {fx rc} SK {PI} B K MT FM_RA CTX roimg.
Check (fun (fx : YK11.FPState) (rc : YM05.RunCeil) (SK : YI16.sink_head) (PI : PAImg pcap_listing)
           B K MT FM_RA CTX roimg =>
         pb_pcap_source_openX_of (fx := fx) (rc := rc) SK (PI := PI) B K MT FM_RA CTX roimg).

Arguments op_entry {fx rc} SK {PI}.
Arguments topen_kept_call {rc} SK {PI}.
Arguments op_at_call {rc} SK {PI}.
Arguments op_to_call {fx rc} SK {PI}.
Arguments pb_pcap_source_openX {fx rc} SK {PI} B K MT FM_RA CTX roimg.
Check (fun (fx : YK11.FPState) (rc : YM05.RunCeil) (SK : YI16.sink_head) (PI : PAImg pcap_listing)
           B K MT FM_RA CTX roimg =>
         pb_pcap_source_openX (fx := fx) (rc := rc) SK (PI := PI) B K MT FM_RA CTX roimg).
Print Assumptions pb_pcap_source_openX.
