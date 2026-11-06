(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the tail of pcap_source_open (fuzz_pcap.asan-ubsan 0x811e0, listing offset
   AF_pcap_source_open = 0xa58, 246 instructions) on libreac v1.9.0's ASan+UBSan build: lib/A's PcapSourceOpenB.v, the
   walk from the two semantic cuts of lib/B/Prog/PcapSourceOpenPh.v to the return. op_from_null and op_from_read prove
   `op_from op_gi_null` and `op_from op_gi_read`, i.e. lib/A's image-generic post tpcap_source_open_post (with
   topen_kept, lib/A/Prog/PcapSourceOpenDefs.v) at this image (SEGS = pa_segs, the relro window pa_relro_lo /
   pa_relro_hi of the lib/B PAImg instance PI); PcapSourceOpen.v (the head) composes them. At ossv/recipes 25e3d17bdb50 (2026-10-29), this image had no released
   proof (rule 24, a Theorem Labs lane, 22:35Z); the released v1.8 UBSan proof lib/U/Prog/pcap_source_open.v is the guard
   template only.

   The paths, at this image's pcs:
   - the empty input (cut 0x813f8, f = NULL): a0 := -1, `j 0x81474`, the epilogue without the buffer re-poison;
   - the short read (cut 0x8138c, kr <> 24): `bne a0,s9` to 0x81400, the shadow test of ps (0x81400 `lbu`, 0x81404
     `bnez`), f = ps->f (0x81408), the fclose wrapper's call (0x8140c), the second shadow test (0x81410, 0x81414
     `beqz` to 0x8145c), ps->f := NULL (0x8145c), a0 := -1, the epilogue from 0x81464 (op_fclose);
   - kr = 24: the UBSan guard G6 (below), the magic of the four header bytes F + 32 .. F + 35 (0x81398..0x813c4, the
     top byte through `slliw`, magic_U), then 0xd4c3b2a1 (0x813c8 `beq` to 0x81420: ps->swapped := 1, a0 := 0,
     `j 0x81464`), 0xa1b2c3d4 (0x813d4 `bne` falls to 0x813d8: ps->swapped := 0, a0 := 0, `j 0x81464`), or the bad
     magic (0x81444: as the short read, fclose at 0x81450);
   - the epilogue (op_epi): the buffer out of scope (0x81464..0x81470, 3 shadow bytes 0xf8), the retired magic
     0x45e0360e at F (0x8147c); 0x81480 `beqz s2` NOT taken (s2 = F >= 4096, atom 18's fact), so the machine-frame
     arm 0x814d4..0x81500 is dead; F's 16 shadow bytes 0xf5 (0x81484..0x814c4); the flag through `ld a1,0x78(s2)` and
     `sb zero,0(a1)` (0x814c8, 0x814cc), which gives the frame back (lib/B/Prog/PcapFrame.v aj_flag_store_pi:
     astack_free_law, frame_flag_lawP); the restores and `ret` (0x81504..0x81538).
   The two guards on ps (G5, 0x812f8 and 0x81300 / 0x81304) are before the cuts, in the head.

   THE GUARD G6. 0x81390 `addi a0,zero,-3`, 0x81394 `bgeu s4,a0` branches to the `unimp` at 0x8153c when the header
   buffer s4 = F + 32 lies within 3 bytes of 2^64. The symbolic run decides it, NOT taken: decide_cond2
   (Reusable/YP0e.v:932) maps BC_GEU to the negation of decide_ltu2 (:922), and decide_ltu (Reusable/YP0m.v:673) finds
   atom 20 (s4) below the literal 2^64 - 3 from its range fact [4128, 0x7fffff800020] (rd_facts), which rd_entry
   proves from frames_bounds on the class-1 frame (F + 128 <= alloc_ceiling <= 0x7fffff800000). Templates: the released
   UBSan proof of the v1.8 image, proofs/libreac/fuzz_pcap/lib/U/Prog/pcap_source_open.v on origin/ossv/recipes
   c8557374ad2e, open_mid :286 (premise bv_unsigned sp0 < 2 ^ 63 at :291, frame bounds :295-299), which decides the
   guard at :410-412; and the earlier walk of this image, on a working branch
   (a8ccd33b1a7) pcap_source_open_tl.v (sha256 4aaa5af08467; internal record) pso_rdchk :36-67 (premise bv_unsigned s4 < 2 ^ 64 - 3 at :44,
   `step; step; if_false` at :65).

   THE REPORT PATHS are proved unreachable; no run steps into one. Every shadow test of ps in this stretch
   (0x81400 / 0x81404 and 0x81410 / 0x81414 on the short read, 0x81444 / 0x81448 and 0x81454 / 0x81458 on the bad
   magic, 0x813e4 / 0x813e8 and 0x8142c / 0x81430 on ps + 8 before the slow checks 0x81570 / 0x81584) is decided by
   the shadow entry of ps (rd_SH: ps's 24 bytes addressable; shent_rd_ok from op_pre's range_addressable, kept to the
   cut by op_mid's topen_kept and across fclose by its journal, shok_transfer), so the token run reads a 0 shadow byte
   and takes the non-report successor: the report calls 0x8141c, 0x81580, 0x81594 and 0x815a0..0x815b4 are never
   reached.

   The callees are Section hypotheses of their exact statement types: the fclose wrapper AFCLOSE, of
   lib/A/Stdio/PFclose.v's image-generic afclose_source_spec (= afclose_source_spec_stk PFCLOSE_STK) at this image,
   bound as lib/B/Prog/PcapSourceClose.v binds it (its data-buffer premise from op_pre's input block); the file meter
   FM (lib/A/Stdio/PSourceMeter.v asrc_file_meter); the frame give-back laws astack_free_law (Reusable/YG0d.v:301) and
   frame_flag_lawP (Reusable/YCbq.v:797) with model_laws; the meter laws (Reusable/YC5d.v ameter_laws,
   ameter_fs_laws); ASIL (lib/A/Stdio/PSourceMeta.v asource_img_laws). The stream predicates' frame lemmas are copied
   from lib/B/Prog/PcapSourceClose.v (not required). getr / mkst / seg_rom come from YK11; nothing from lib/Lib is
   imported. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/B/Prog/PcapSourceOpenB.v, with its module paths, module names and numbers changed; 660 of its 725 lines of code are new or changed and 1681 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/fuzz_recv_entry.v, with its module names changed; 667 of its 749 lines of code are new or changed and 643 lines of the source are left out. *)
(* check_requests on image A (fuzz_link.asan 0x869a8, listing offset AF_check_requests = 0x47dc; listing
   (internal path) (internal record, sha256 da0e135719be)): the walk of its contract
   lib/A/Prog/check_requests_c.v `check_requests_acontract` (link_amem.v `aleaf_rd`, K = 80 + 2 * ESTACK = 8272,
   EV 0, SIDE [], write set []).

   +0x00..+0x28 push the 80-byte frame (ra, s0..s8); +0x2c..+0x60 the shadow base, s5 := n_sent; +0x4c..+0x68 the
   instrumented check of n_req at m + 8336 (the entry state's shadow entry rq_SH) and the load; +0x6c `bne s5, a1`
   decided equal (n_sent and n_req are the one atom 33, requests_are); +0x70 `blez s5`: decided by the entry state's
   range of atom 33 (n = 0: return; n > 0: the loop). The loop head +0xb0 after i turns is check_requests_kit.v's
   rq_lss (rq_seat): the checks of sent_len[i] and req_len[i] (shadow entries), the two loads (one atom L,
   requests_are), `bne` decided equal, a2 := min(L, 512) = L (nlk_wf: L <= 512; both arms of `bltu`), then
   wrapper_bcmp(sent[i], req[i], L) (0x4305c, LinkWalkBcmp.v aj_gx_bcmp_at): requests_are makes the two byte ranges
   equal (rq_bytes), so a0 = 0 and +0xec falls through; +0xf0..+0x110 the cursors move, `bnez s5` back to +0xb0
   (rq_loop's induction on the turns left) or to the epilogue +0x114..+0x140, ret. The run and bcmp write only
   [sp - 8272, sp) (LinkWalkNoWrite.v), so the Post (True) closes with lf_finish0.

   Section hypotheses: LAWS, TL (PALib), LV (LinkVals) are the image instance's facts; BCMP (Reusable/YG0d.v
   abcmp_realizes at the wrapper) is discharged on the image by lib/A/AE2s.v `bcmp_icpt_contract` from the image's
   asyms record (check_requests_aproof_img).

   Proves check_requests (kind: function proof). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC81 YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk LinkWalkNoWrite LinkWalkNlk LinkWalkBcmp check_requests_c check_requests_kit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AB1v AF0m AE2s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YG0q.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Lemma rq_denot_shx_g : forall E m c v sb, ew E m = Z_to_bv 64 v -> ew E 32 = Z_to_bv 64 sb ->
  0 <= v < 2 ^ 63 -> 0 <= v + c < 2 ^ 63 -> 0 <= sb < 2 ^ 32 ->
  sv_denot E (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SOff m c) (SLit 3))) = Z_to_bv 64 (sb + (v + c) / 8).
Proof.
intros E m c v sb Hv Hs Hv0 Hvc Hs0. apply bv_eq.
change (U E (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SOff m c) (SLit 3))) = bv_unsigned (Z_to_bv 64 (sb + (v + c) / 8))).
rewrite !U_SAlu, lf_U_reg, U_SOff, U_SLit, Hv, Hs. rewrite !unsigned_lit_small by lia.
cbn [zalu_raw]. change (zcanon 3) with 3. change (Z.land 3 63) with 3. unfold zcanon, M64.
rewrite (Z.mod_small (v + c)) by lia.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
pose proof (Z.div_pos (v + c) 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound (v + c) 8 (v + c) ltac:(lia) ltac:(lia)).
rewrite (Z.mod_small ((v + c) / 8)) by lia. apply Z.mod_small. lia.
Qed.

Lemma rq_denot_shx1 : forall E v sb, ew E 34 = Z_to_bv 64 v -> ew E 32 = Z_to_bv 64 sb ->
  0 <= v < 2 ^ 63 -> 0 <= sb < 2 ^ 32 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SOff 34 0) (SLit 3))) (SLit 1))
    = Z_to_bv 64 (sb + v / 8 + 1).
Proof.
intros E v sb Hv Hs Hv0 Hs0. apply bv_eq.
change (U E (SAlu ALU_ADD (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SOff 34 0) (SLit 3))) (SLit 1))
  = bv_unsigned (Z_to_bv 64 (sb + v / 8 + 1))).
rewrite !U_SAlu, !lf_U_reg, !U_SLit, Hv, Hs. rewrite !unsigned_lit_small by lia.
cbn [zalu_raw]. change (zcanon 3) with 3. change (zcanon 1) with 1. change (Z.land 3 63) with 3. unfold zcanon, M64.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
pose proof (Z.div_pos v 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound v 8 v ltac:(lia) ltac:(lia)).
rewrite (Z.mod_small (v / 8)) by lia. rewrite (Z.mod_small (sb + v / 8)) by lia. apply Z.mod_small. lia.
Qed.

Lemma rq_ne_zero : forall E n (r : word), ew E n = r -> r = w64 0 ->
  branch_taken BC_NE (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = true -> False.
Proof. intros E n r Er Hr Hc. rewrite branch_ne_U, lf_U_reg, U_SLit, Er, Hr in Hc. vm_compute in Hc. discriminate. Qed.

Lemma rq_grows_of_present : forall H m m',
  (forall a, apresent H m a -> apresent H m' a) -> mem_grows (mrestrict H m) (mrestrict H m').
Proof.
intros H m m' Hp x Hx. unfold mrestrict in *. destruct (H x) eqn:Eh; [exact Hx|].
destruct (m x) as [b|] eqn:Em; [|exfalso; exact (Hx eq_refl)].
assert (Ha : apresent H m (bv_unsigned x)).
{ unfold apresent. rewrite Z_to_bv_bv_unsigned. split; [exact Eh | exists b; exact Em]. }
destruct (Hp _ Ha) as [_ [b' Hb']]. rewrite Z_to_bv_bv_unsigned in Hb'. rewrite Hb'. discriminate.
Qed.

Lemma rq_shadow_low : forall x, 0 <= x < 2 ^ 47 -> 0 <= shadow_addr x < 2 ^ 45.
Proof. intros x Hx. unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_lt_upper_bound x 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia. Qed.

(* the shadow hull of a sub-range lies in the hull of the range *)
Lemma rq_hull_sub : forall (rd : reader) a n a' n',
  shadow_hull_vis rd a n -> a <= a' -> 0 < n' -> a' + n' <= a + n -> shadow_hull_vis rd a' n'.
Proof.
intros rd a n a' n' H H1 H2 H3 s Hs. apply H. unfold shadow_addr, SHADOW_OFF in *.
pose proof (Z.div_le_mono a a' 8 ltac:(lia) H1).
pose proof (Z.div_le_mono (a' + n' - 1) (a + n - 1) 8 ltac:(lia) ltac:(lia)).
pose proof (Z.div_le_mono (2147450880 + a / 8) (2147450880 + a' / 8) 8 ltac:(lia) ltac:(lia)).
pose proof (Z.div_le_mono (2147450880 + (a' + n' - 1) / 8) (2147450880 + (a + n - 1) / 8) 8 ltac:(lia) ltac:(lia)).
lia.
Qed.

Lemma rq_val_frame : forall segs (m m' : word -> option byte) a (n : nat) v,
  val_mem segs m a n v -> (forall x, a <= x < a + Z.of_nat n -> mbyte segs m' x = mbyte segs m x) ->
  val_mem segs m' a n v.
Proof. intros segs m m' a n v HV HK j Hj. rewrite (HK (a + Z.of_nat j) ltac:(lia)). exact (HV j Hj). Qed.

Lemma rq_nth_slice : forall (bs : list byte) off n k, 0 <= off -> 0 <= k < n ->
  nth_error (slice bs off n) (Z.to_nat k) = nth_error bs (Z.to_nat (off + k)).
Proof.
intros bs off n k H0 Hk. unfold slice. rewrite lw_nth_error_firstn by lia. rewrite lw_nth_error_skipn.
f_equal. lia.
Qed.

Lemma rq_grow : forall (H : word -> bool) (m m' : word -> option byte),
  mem_grows (mrestrict H m) (mrestrict H m') -> forall a, apresent H m a -> apresent H m' a.
Proof.
  intros H m m' HG a (Hh & b & Hb). split; [exact Hh|].
  specialize (HG (Z_to_bv 64 a)). unfold mrestrict in HG. rewrite Hh, Hb in HG.
  destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:E; [exists b'; reflexivity|].
  exfalso. apply HG; [discriminate | reflexivity].
Qed.

(* the bytes a run left as they were: the loop's runs write nothing *)
Ltac rq_nokept HFr W UNn :=
  let sg := lazymatch type of W with world ?s => s end in
  pose proof (kept_of_frame (segs := sg) _ _ _ _ _ (fun _ : Z => False) HFr
    ltac:(let bb := fresh in let wl := fresh in let wh := fresh in let aa := fresh in
          let Hin := fresh in let Hrr := fresh in let H0 := fresh in
          intros bb wl wh aa Hin Hrr; vm_compute in Hin;
          repeat (destruct Hin as [H0 | Hin];
                  [ inversion H0; subst; cbn [base_val] in Hrr; exfalso; lia | ]);
          exact Hin)) as UNn.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation VAL := (@pa_val _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis LV : LinkVals.
Hypothesis BCMP : abcmp_realizes SEGS B (pa_sigma LS___interceptor_trampoline_bcmp).

(* bcmp's two ranges hold the same bytes: requests_are *)
Lemma rq_bytes : forall (W : world SEGS) memc mT kbs mbs mp i j sp,
  anlk_at SEGS (rdW W memc) LA_G_NL kbs -> amodel_at SEGS (rdW W memc) mp mbs -> requests_are kbs mbs ->
  0 <= i < nk_n_sent kbs -> nk_n_sent kbs <= 16 -> 0 <= mp -> mp + MD_SIZE <= 2 ^ 47 ->
  0 <= j < fld_u64 kbs (NK_SENT_LEN + 8 * i) -> fld_u64 kbs (NK_SENT_LEN + 8 * i) <= 512 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ lf_Zs 8272 sp a -> aview SEGS (w_H W) mT a = aview SEGS (w_H W) memc a) ->
  2 ^ 46 <= sp - 8272 -> (mp + MD_SIZE <= sp - 8272 \/ sp <= mp) ->
  aview SEGS (w_H W) mT (RQ_SD + 512 * i + j) = aview SEGS (w_H W) mT (mp + MD_REQ + 512 * i + j).
Proof.
intros W memc mT kbs mbs mp i j sp HNK HMD HRQ Hi Hn Hmp0 Hmp1 Hj HL UN Hsp Hapf.
destruct HRQ as (Heqn & HRQ). destruct (HRQ i Hi) as (HLen & HOne).
destruct HNK as [[[_ [_ Hk]] _] HkL]. destruct HMD as [[[_ [_ Hm]] _] HmL].
assert (HNKs : NK_SIZE = 271992) by reflexivity. assert (HMDs : MD_SIZE = 8856) by reflexivity.
unfold lf_Zs in UN. unfold RQ_SD, NK_SENT, MD_REQ in *.
rewrite !UN by (unfold LA_G_NL; lia).
rewrite <- !(ard_aview SEGS). unfold ard. f_equal.
replace (LA_G_NL + 262692 + 512 * i + j) with (LA_G_NL + Z.of_nat (Z.to_nat (262692 + 512 * i + j))) by lia.
replace (mp + 12 + 512 * i + j) with (mp + Z.of_nat (Z.to_nat (12 + 512 * i + j))) by lia.
rewrite (Hk (Z.to_nat (262692 + 512 * i + j))) by (unfold LA_G_NL in *; lia).
rewrite (Hm (Z.to_nat (12 + 512 * i + j))) by lia.
unfold nk_sent_one, md_req_one in HOne. rewrite <- HLen in HOne.
pose proof (f_equal (fun l => nth_error l (Z.to_nat j)) HOne) as Hn2. cbv beta in Hn2.
rewrite (rq_nth_slice kbs (NK_SENT + NL_SENT_LEN * i) _ j) in Hn2 by (unfold NK_SENT, NL_SENT_LEN; lia).
rewrite (rq_nth_slice mbs (MD_REQ + NL_SENT_LEN * i) _ j) in Hn2 by (unfold MD_REQ, NL_SENT_LEN; lia).
unfold NK_SENT, MD_REQ, NL_SENT_LEN in Hn2. exact Hn2.
Qed.


(* the shadow entries of the loop head at any memory that keeps the two 8-byte cells' shadow *)
Lemma rq_shok : forall (E : env) (W : world SEGS) (mem : word -> option byte) i mp,
  ew E 32 = Z_to_bv 64 SB -> ew E 34 = Z_to_bv 64 (RQ_SL + 8 * i) -> ew E 35 = Z_to_bv 64 (mp + MD_REQ_LEN + 8 * i) ->
  0 <= i < 16 -> 0 <= mp -> amem_range mp MD_SIZE ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (RQ_SL + 8 * i) 8 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (mp + MD_REQ_LEN + 8 * i) 8 ->
  sh_ok SEGS (SOff 32 0) rq_LSH E (rdW W mem).
Proof.
intros E W mem i mp X32 X34 X35 Hi Hmp Hamr RA1 RA2.
assert (HSL : RQ_SL = 6417640) by reflexivity. assert (HSBb : SB = 2147450880) by reflexivity.
assert (HMD : MD_SIZE = 8856 /\ MD_REQ_LEN = 8208) by (split; reflexivity). destruct HMD as (HMD1 & HMD2).
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr.
unfold rq_LSH. repeat apply Forall_cons; try apply Forall_nil;
  unfold shent_ok, app_apart; cbn [she_m she_lo she_hi];
  rewrite (U_atom E 32 SB X32) by lia; rewrite ?Z.add_0_r, ?Z.sub_0_r, ?Z.min_l, ?Z.max_r by lia.
- rewrite (U_atom E 34 (RQ_SL + 8 * i) X34) by lia. split; [rewrite <- (aview_rd_of SEGS); exact RA1|].
  intros a Ha. lia.
- rewrite (U_atom E 35 (mp + MD_REQ_LEN + 8 * i) X35) by lia. split; [rewrite <- (aview_rd_of SEGS); exact RA2|].
  intros a Ha. lia.
Qed.

(* THE LOOP at +0xb0: one turn per sent request, by induction on the turns left *)
Lemma rq_loop :
 forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) kbs mbs,
  gx_ok SEGS B G ->
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  YK0s.ret_ok (getr regs 1) ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - 8272 -> spZ regs <= sp0 ->
  anlk_at SEGS (rdW W memc) LA_G_NL kbs -> amodel_at SEGS (rdW W memc) (aarg regs 0) mbs ->
  nlk_wf kbs -> requests_are kbs mbs ->
  range_addressable (ard SEGS (rdW W memc)) SHADOW_OFF (aarg regs 0) MD_SIZE ->
  shadow_hull_vis (ard SEGS (rdW W memc)) (aarg regs 0) MD_SIZE ->
  amem_range (aarg regs 0) MD_SIZE ->
  range_addressable (ard SEGS (rdW W memc)) SHADOW_OFF LA_G_NL NK_SIZE ->
  shadow_hull_vis (ard SEGS (rdW W memc)) LA_G_NL NK_SIZE ->
  apart_frame regs 8272 (aarg regs 0) MD_SIZE ->
  apart_gnl LA_G_NL (aarg regs 0) MD_SIZE ->
  forall (ni : nat) (i : Z) (mem1 : word -> option byte) (md1 : Model) (regs1 : bvmap 5 word),
  (Z.to_nat (nk_n_sent kbs - i) = ni)%nat -> 0 <= i -> i < nk_n_sent kbs ->
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem1 md1 k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ lf_Zs 8272 (spZ regs) a -> aview SEGS (w_H W) mem1 a = aview SEGS (w_H W) memc a) ->
  mem_grows (rdW W memc) (rdW W mem1) ->
  m_fds md1 = m_fds mdc -> m_fs md1 = m_fs mdc ->
  rq_inv regs regs1 (nk_n_sent kbs) i (aarg regs 0) -> rq_saved W mem1 regs ->
  SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + (AF_check_requests + 0xb0))) mem1 (seg_rom SEGS)) md1)
    (apost SK SEGS B 8272 0 (fun a => inFP [] a)
       G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
       (fun ly2 S2 W2 regs2 mem2 md2 =>
          S2 = set_fs (st_fs S2) Sc /\ Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\ True)).
Proof.
intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs kbs mbs
  HGX HJ0 Hret Hgp Htp H16 Hwlo Hwhi HNK HMD WF HRQ RAM HUM AMR RAG HUG HAPF HAPG.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
pose proof HJ0 as (HSTK0 & HXO0 & (memS0 & HJi0 & _) & _).
pose proof HJi0 as (HAR0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
assert (Hsp46 : 2 ^ 46 <= spZ regs - 8272 /\ spZ regs <= 2 ^ 47) by lia.
assert (HSL : RQ_SL = 6417640) by reflexivity. assert (HSD : RQ_SD = 6409444) by reflexivity.
assert (HSBb : SB = 2147450880) by reflexivity. assert (HGb : LA_G_NL = 6146752) by reflexivity.
assert (HMD1 : MD_SIZE = 8856) by reflexivity. assert (HMD2 : MD_REQ_LEN = 8208) by reflexivity.
assert (HMD3 : MD_REQ = 12) by reflexivity. assert (HNKs : NK_SIZE = 271992) by reflexivity.
unfold apart_frame, apart_gnl in HAPF, HAPG.
pose proof WF as (_ & _ & Wns & _ & _ & _ & _ & _ & _ & _ & _ & _ & Wsl). unfold NL_SENT_MAX in Wns.
pose proof HRQ as (Heqn & HRQi).
set (n := nk_n_sent kbs) in *. set (mp := aarg regs 0) in *.
assert (Hmp : 0 <= mp /\ mp + MD_SIZE <= 2 ^ 47 - 1).
{ split.
  - unfold mp, aarg, argZ. apply bv_unsigned_in_range.
  - unfold amem_range in AMR. unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in AMR. rewrite HMD1 in *. lia. }
pose proof (paj_run_x SK B LAWS G HGX XO OUT) as RUN.
pose proof (paj_run_to_x SK B LAWS G HGX XO OUT) as RUNTO.
pose proof (paj_branch (PI := PI)) as BR.
intros ni; induction ni as [|ni IH];
  intros i mem1 md1 regs1 Hni Hi0 Hilt HJ1 UN HGc Hfd1 Hfs1 HINV HSV; [exfalso; lia|].
(* the turn's length, its two cells and their shadows at mem1 *)
set (L := fld_u64 kbs (NK_SENT_LEN + 8 * i)).
destruct (HRQi i ltac:(lia)) as (HLm & HOne).
assert (HL : 0 <= L <= 512) by (exact (Wsl i ltac:(lia))).
assert (Hm1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 8272 <= a < spZ regs) ->
          mbyte SEGS (rdW W mem1) a = mbyte SEGS (rdW W memc) a)
  by (intros a Ha Hw; apply (mbyte_of_aview SEGS); apply UN; [exact Ha | unfold lf_Zs; exact Hw]).
assert (VL1 : val_mem SEGS (rdW W mem1) (RQ_SL + 8 * i) 8 L).
{ apply (rq_val_frame SEGS (rdW W memc)).
  - unfold RQ_SL. rewrite <- Z.add_assoc. exact (anlk_field SEGS (rdW W memc) LA_G_NL kbs (NK_SENT_LEN + 8 * i) 8 HNK
      ltac:(unfold NK_SENT_LEN; lia) ltac:(unfold NK_SENT_LEN; lia)).
  - intros x Hx. apply Hm1; lia. }
assert (VL2 : val_mem SEGS (rdW W mem1) (mp + MD_REQ_LEN + 8 * i) 8 L).
{ apply (rq_val_frame SEGS (rdW W memc)).
  - destruct HMD as [[Hab _] HmL]. rewrite <- Z.add_assoc. unfold L. rewrite HLm.
    exact (val_mem_of_abytes SEGS (rdW W memc) mp mbs (MD_REQ_LEN + 8 * i) 8 Hab ltac:(lia) ltac:(lia)).
  - intros x Hx. apply Hm1; lia. }
assert (UNs : forall x, 0 <= x < 2 ^ 47 -> aview SEGS (w_H W) mem1 (shadow_addr x) = ard SEGS (rdW W memc) (shadow_addr x))
  by (intros x Hx; pose proof (rq_shadow_low x Hx); rewrite (ard_aview SEGS); apply UN; [lia | unfold lf_Zs; lia]).
assert (RA1 : range_addressable (aview SEGS (w_H W) mem1) SHADOW_OFF (RQ_SL + 8 * i) 8).
{ apply (ra_shadow_eq (ard SEGS (rdW W memc))); [intros x Hx; apply RAG; lia | intros x Hx; apply UNs; lia]. }
assert (RA2 : range_addressable (aview SEGS (w_H W) mem1) SHADOW_OFF (mp + MD_REQ_LEN + 8 * i) 8).
{ apply (ra_shadow_eq (ard SEGS (rdW W memc))); [intros x Hx; apply RAM; lia | intros x Hx; apply UNs; lia]. }
destruct (rq_seat SK B AF_check_requests G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem1 md1 k regs regs1
            n i mp L HJ1 H16 ltac:(change CHECK_REQUESTS_AK with 8272; lia) Hwhi HINV HSV
            ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HL VL1 VL2 ltac:(lia)
            ltac:(change CHECK_REQUESTS_AK with 8272; lia) AMR RA1 RA2) as (HS & SHOK).
pose proof (rq_E_img regs regs1 n i mp L) as HEI.
set (E := rq_E regs regs1 n i mp L) in *.
assert (XX32 : ew E 32 = Z_to_bv 64 SB) by exact (rq_E_ext _ _ _ _ _ _ 0%nat ltac:(lia)).
assert (XX33 : ew E 33 = Z_to_bv 64 (n - i)) by exact (rq_E_ext _ _ _ _ _ _ 1%nat ltac:(lia)).
assert (XX34 : ew E 34 = Z_to_bv 64 (RQ_SL + 8 * i)) by exact (rq_E_ext _ _ _ _ _ _ 2%nat ltac:(lia)).
assert (XX35 : ew E 35 = Z_to_bv 64 (mp + MD_REQ_LEN + 8 * i)) by exact (rq_E_ext _ _ _ _ _ _ 3%nat ltac:(lia)).
assert (XX36 : ew E 36 = Z_to_bv 64 (RQ_SD + 512 * i)) by exact (rq_E_ext _ _ _ _ _ _ 4%nat ltac:(lia)).
assert (XX37 : ew E 37 = Z_to_bv 64 (mp + MD_REQ + 512 * i)) by exact (rq_E_ext _ _ _ _ _ _ 5%nat ltac:(lia)).
assert (XX38 : ew E 38 = Z_to_bv 64 L) by exact (rq_E_ext _ _ _ _ _ _ 6%nat ltac:(lia)).
assert (ER : forall (m : nat) (r : bv 5), Z.of_nat m = bv_unsigned r -> (m < 32)%nat -> ew E m = getr regs r)
  by (intros m r Hm Hl; apply rq_E_reg; assumption).
assert (EE1 : ew E 1 = getr regs 1) by (apply ER; [reflexivity | lia]).
assert (EE2 : ew E 2 = getr regs 2) by (apply ER; [reflexivity | lia]).
assert (EE3 : ew E 3 = getr regs 3) by (apply ER; [reflexivity | lia]).
assert (EE4 : ew E 4 = getr regs 4) by (apply ER; [reflexivity | lia]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite EE2; reflexivity).
assert (U34 : bv_unsigned (ew E 34) = RQ_SL + 8 * i) by (rewrite XX34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = mp + MD_REQ_LEN + 8 * i) by (rewrite XX35; apply unsigned_lit_small; lia).
(* +0xb0 .. +0xd8: the two checks, the two loads, `bltu` *)
paj_run_tok RUN HS HJ1 SHOK Bspan; [lf_awr |].
rq_nokept HFr W UF1.
lf_kept HFr W 8272 (spZ regs) UNk. clear HF HFr. lf_fold UN HGc UNk HG W memc 8272 (spZ regs).
psrr_branch_tok RUN BR HS SHOK Bspan.
(* +0xe0 .. +0xe8: the arguments of bcmp; a2 = L on both arms (L <= 512) *)
all: assert (HLa : L < 512 \/ L = 512) by lia.
all: paj_run_tok RUN HS HJ1 SHOK Bspan; [lf_awr |].
all: rq_nokept HFr W UF2.
all: lf_kept HFr W 8272 (spZ regs) UNk; clear HF HFr; lf_fold UN HGc UNk HG W memc 8272 (spZ regs).
all: lazymatch type of HS with st_ok _ _ _ (restrict _ ?msC) => rename msC into msA end.
all: pmkst HS.
all: prreg HS (1%bv : bv 5) Q1; prreg HS (2%bv : bv 5) Q2; prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4;
  prreg HS (10%bv : bv 5) Q10; prreg HS (11%bv : bv 5) Q11; prreg HS (12%bv : bv 5) Q12.
all: assert (Hn12 : getr (ms_regs msA) 12 = w64 L);
  [ first
    [ rewrite Q12, XX38; reflexivity
    | rewrite Q12; rewrite branch_ltu_U, lf_U_reg, U_SLit, XX38, unsigned_lit_small in Hc by lia;
      change (zcanon 512) with 512 in Hc; apply Z.ltb_ge in Hc; unfold w64; f_equal; lia ] | ].
all: assert (Hspa : spZ (ms_regs msA) = spZ regs - 80)
  by (unfold spZ at 1; rewrite Q2; first [rewrite EE2 | idtac]; rewrite ?Usp; apply unsigned_lit_small; lia).
all: assert (UNa : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 8272 <= a < spZ regs) ->
              aview SEGS (w_H W) (ms_mem msA) a = aview SEGS (w_H W) memc a)
  by (intros a Ha Hw; apply UN; [exact Ha | unfold lf_Zs; exact Hw]).
all: eapply SRr_bind;
  [ eapply (aj_gx_bcmp_at SK SEGS B LAWS pa_segs_low _ BCMP G XO OUT W (ms_regs msA) (ms_mem msA) STK sp0 FP ly S
      W0 mem0 md0 own lyc Sc _ k (RQ_SD + 512 * i) (mp + MD_REQ + 512 * i) L _ HGX HJ1);
    [ rewrite Hspa; lia
    | rewrite Hspa; change ESTACK with 4096; lia
    | rewrite Hspa; lia
    | rewrite Q3, EE3; exact Hgp
    | rewrite Q4, EE4; exact Htp
    | exact Q1
    | apply ret_ok_codeptr_v; lia
    | rewrite Q10, XX36; reflexivity
    | rewrite Q11, XX37; reflexivity
    | exact Hn12
    | lia | lia | lia | lia | lia
    | intros a Ha; rewrite Hspa; change ESTACK with 4096; split; [|lia];
      rewrite UNa by lia; rewrite <- (ard_aview SEGS); unfold ard;
      destruct HNK as [[[_ [_ Hk]] _] HkL];
      replace a with (LA_G_NL + Z.of_nat (Z.to_nat (a - LA_G_NL))) by lia;
      rewrite (Hk (Z.to_nat (a - LA_G_NL))) by (unfold RQ_SD, NK_SENT in Ha; lia);
      destruct (nth_error kbs (Z.to_nat (a - LA_G_NL))) eqn:Eb; [discriminate | apply nth_error_None in Eb; lia]
    | intros a Ha; rewrite Hspa; change ESTACK with 4096; split; [|lia];
      rewrite UNa by lia; rewrite <- (ard_aview SEGS); unfold ard;
      destruct HMD as [[[_ [_ Hk]] _] HkL];
      replace a with (mp + Z.of_nat (Z.to_nat (a - mp))) by lia;
      rewrite (Hk (Z.to_nat (a - mp))) by lia;
      destruct (nth_error mbs (Z.to_nat (a - mp))) eqn:Eb; [discriminate | apply nth_error_None in Eb; lia]
    | intros a Ha; rewrite Hspa; change ESTACK with 4096; lia
    | intros a Ha; rewrite Hspa; change ESTACK with 4096; lia
    | unfold amem_range, kLowMemEnd; lia
    | unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia
    | apply (ra_shadow_eq (ard SEGS (rdW W memc))); [intros x Hx; apply RAG; lia |];
      intros x Hx; pose proof (rq_shadow_low x ltac:(lia)); rewrite (ard_aview SEGS); apply UNa; lia
    | intros Hn s Hs; pose proof (rq_shadow_low (RQ_SD + 512 * i) ltac:(lia)) as S0;
      pose proof (rq_shadow_low (RQ_SD + 512 * i + L - 1) ltac:(lia)) as S1;
      rewrite UNa; [rewrite <- (ard_aview SEGS); exact (rq_hull_sub _ _ _ (RQ_SD + 512 * i) L HUG ltac:(lia) Hn ltac:(lia) s Hs)
                   | unfold shadow_addr, SHADOW_OFF in *; lia | unfold shadow_addr, SHADOW_OFF in *; lia]
    | apply (ra_shadow_eq (ard SEGS (rdW W memc))); [intros x Hx; apply RAM; lia |];
      intros x Hx; pose proof (rq_shadow_low x ltac:(lia)); rewrite (ard_aview SEGS); apply UNa; lia
    | intros Hn s Hs; pose proof (rq_shadow_low (mp + MD_REQ + 512 * i) ltac:(lia)) as S0;
      pose proof (rq_shadow_low (mp + MD_REQ + 512 * i + L - 1) ltac:(lia)) as S1;
      rewrite UNa; [rewrite <- (ard_aview SEGS); exact (rq_hull_sub _ _ _ (mp + MD_REQ + 512 * i) L HUM ltac:(lia) Hn ltac:(lia) s Hs)
                   | unfold shadow_addr, SHADOW_OFF in *; lia | unfold shadow_addr, SHADOW_OFF in *; lia] ]
  | ].
(* after bcmp: the two ranges are equal, so a0 = 0 *)
all: cbv beta; intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hiff & Hkeep & Hpres2 & Hsm).
all: assert (Hz : getr regs2 10 = w64 0)
  by (apply (proj2 Hiff); intros j Hj;
      exact (rq_bytes W memc (ms_mem msA) kbs mbs mp i j (spZ regs) HNK HMD HRQ (conj Hi0 Hilt) (proj2 Wns)
               (proj1 Hmp) ltac:(lia) Hj (proj2 HL) UNa ltac:(lia) HAPF)).
all: assert (FRA : forall a, spZ regs - 80 <= a < spZ regs ->
              aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem1 a)
  by (intros a Ha; rewrite Hkeep by (first [lia | rewrite Hspa; change ESTACK with 4096; lia]);
      rewrite (UF2 a ltac:(lia) ltac:(intros [])); exact (UF1 a ltac:(lia) ltac:(intros []))).
all: assert (UN2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 8272 <= a < spZ regs) ->
              aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a)
  by (intros a Ha Hw; rewrite Hkeep by (first [exact Ha | rewrite Hspa; change ESTACK with 4096; lia]);
      exact (UNa a Ha Hw)).
all: assert (HGc2 : mem_grows (rdW W memc) (rdW W mem2))
  by (apply rq_grows_of_present; intros a Ha; apply Hpres2; exact (rq_grow _ _ _ HGc a Ha)).
all: jafter_call_keep_pi HS 64%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2]%nat HS2.
all: lazymatch type of HS2 with ?Q -> _ => assert (HKEEP : Q) end;
  [ apply Forall_cons;
    [ eapply (region_kept_aview _ (w_H W) (ms_mem msA) mem2 2%nat (spZ regs) (-80) 0 0 0 _);
      [ first [exact Usp | rewrite ?ew_ewset_other by lia; exact Usp]
      | intros a Ha; apply Hkeep; [lia | rewrite Hspa; change ESTACK with 4096; lia]
      | exact Hpres2 ] | ];
    apply Forall_cons;
    [ eapply (region_kept_aview _ (w_H W) (ms_mem msA) mem2 34%nat (RQ_SL + 8 * i) 0 8 0 0 _);
      [ first [exact U34 | rewrite ?ew_ewset_other by lia; exact U34]
      | intros a Ha; apply Hkeep; [lia | rewrite Hspa; change ESTACK with 4096; lia]
      | exact Hpres2 ] | ];
    apply Forall_cons; [|apply Forall_nil];
    eapply (region_kept_aview _ (w_H W) (ms_mem msA) mem2 35%nat (mp + MD_REQ_LEN + 8 * i) 0 8 0 0 _);
    [ first [exact U35 | rewrite ?ew_ewset_other by lia; exact U35]
    | intros a Ha; apply Hkeep; [lia | rewrite Hspa; change ESTACK with 4096; lia]
    | exact Hpres2 ]
  | specialize (HS2 HKEEP); clear HKEEP ].
all: rewrite <- restrict_mkst_fx in HS2.
all: lazymatch type of HS2 with st_ok_pi _ _ ?EV _ _ => set (E2 := EV) in * end.
all: assert (EW2 : forall a, (a < 64)%nat -> ew E2 a = ew E a)
  by (intros a Ha; unfold E2; rewrite ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; reflexivity).
all: assert (E68 : ew E2 68 = getr regs2 10) by (unfold E2; reflexivity).
all: assert (HEI2 : img_env VAL A_LIM E2)
  by (unfold E2; apply img_env_havoc; [first [exact HEI | apply img_env_ewset; [exact HEI | cbv; lia]] | cbv; lia]).
all: assert (SHOK2 : sh_ok SEGS (SOff 32 0) rq_LSH E2 (mrestrict (w_H W) mem2));
  [ apply (rq_shok E2 W mem2 i mp);
    [ rewrite EW2 by lia; exact XX32 | rewrite EW2 by lia; exact XX34 | rewrite EW2 by lia; exact XX35
    | lia | exact (proj1 Hmp) | exact AMR
    | apply (ra_shadow_eq (ard SEGS (rdW W memc))); [intros x Hx; apply RAG; lia |];
      intros x Hx; pose proof (rq_shadow_low x ltac:(lia)); rewrite (ard_aview SEGS); apply UN2; lia
    | apply (ra_shadow_eq (ard SEGS (rdW W memc))); [intros x Hx; apply RAM; lia |];
      intros x Hx; pose proof (rq_shadow_low x ltac:(lia)); rewrite (ard_aview SEGS); apply UN2; lia ]
  | ].
(* +0xec `bnez a0`: refuted *)
all: psrr_branch_tok RUN BR HS2 SHOK2 Bspan.
all: try (match goal with H : branch_taken BC_NE (sv_denot _ (SOff 68 0)) _ = true |- _ =>
            exfalso; exact (rq_ne_zero E2 68 _ E68 Hz H) end).
(* +0xf0 .. +0x110: the cursors move; `bnez s5` *)
all: paj_run_tok RUN HS2 HJ2 SHOK2 Bspan; [lf_awr |].
all: rq_nokept HFr W UF3.
all: pose proof (rq_grow _ _ _ HG) as GR3; clear HF HFr HG.
all: lazymatch type of HS2 with st_ok_pi _ _ ?EV _ (restrict _ ?msF) => rename msF into msC; set (E3 := EV) in * end.
all: assert (EW3 : forall a, (a < 64)%nat -> ew E3 a = ew E a)
  by (intros a Ha; unfold E3; rewrite ?ew_ewset_other by lia; apply EW2; exact Ha).
all: assert (U33 : U E3 (SOff 33 (-1)) = n - i - 1)
  by (rewrite U_SOff, EW3 by lia; rewrite XX33, unsigned_lit_small by lia; apply YP0m.zcanon_small; lia).
all: assert (UN3 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 8272 <= a < spZ regs) ->
              aview SEGS (w_H W) (ms_mem msC) a = aview SEGS (w_H W) memc a)
  by (intros a Ha Hw; rewrite (UF3 a Ha ltac:(intros [])); exact (UN2 a Ha Hw)).
all: assert (FRC : forall a, spZ regs - 80 <= a < spZ regs ->
              aview SEGS (w_H W) (ms_mem msC) a = aview SEGS (w_H W) mem1 a)
  by (intros a Ha; rewrite (UF3 a ltac:(lia) ltac:(intros [])); exact (FRA a Ha)).
all: assert (HGc3 : mem_grows (rdW W memc) (rdW W (ms_mem msC)))
  by (apply rq_grows_of_present; intros a Ha; apply GR3; exact (rq_grow _ _ _ HGc2 a Ha)).
all: psrr_branch_tok RUN BR HS2 SHOK2 Bspan.
all: match goal with H : branch_taken BC_NE (sv_denot _ (SOff 33 (-1))) _ = ?bb |- _ =>
       rewrite branch_ne_U, U33, (U_lit E3 0) in H by lia; rename H into Hb5 end.
all: first [apply negb_false_iff, Z.eqb_eq in Hb5 | apply negb_true_iff, Z.eqb_neq in Hb5].
(* END: no request left; +0x114 .. +0x140 restore, pop, ret *)
all: lazymatch type of Hb5 with _ = 0 => (paj_run_tok RUN HS2 HJ2 SHOK2 Bspan; [lf_awr |];
       rq_nokept HFr W UF4; pose proof (rq_grow _ _ _ HG) as GR4; clear HF HFr HG;
       lazymatch type of HS2 with st_ok_pi _ _ ?EV _ (restrict _ ?msF) => rename msF into msD; set (E4 := EV) in * end;
       assert (UN4 : forall a, 0 <= a < 2 ^ 64 -> ~ lf_Zs 8272 (spZ regs) a ->
                 aview SEGS (w_H W) (ms_mem msD) a = aview SEGS (w_H W) memc a)
         by (intros a Ha Hw; rewrite (UF4 a Ha ltac:(intros [])); exact (UN3 a Ha Hw));
       assert (HGc4 : mem_grows (rdW W memc) (rdW W (ms_mem msD)))
         by (apply rq_grows_of_present; intros a Ha; apply GR4; exact (rq_grow _ _ _ HGc3 a Ha));
       assert (HAE4 : env_agree 32 (Ereg regs (rq_extra regs1 n i mp L)) E4)
         by (split; [intros nn Hnn; unfold E4; rewrite ?ew_ewset_other by lia; rewrite EW3 by lia;
                     unfold E, rq_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]);
       assert (E41 : ew E4 1 = getr regs 1)
         by (unfold E4; rewrite ?ew_ewset_other by lia; rewrite EW3 by lia; exact EE1);
       lf_ret PI LAWS W regs (rq_extra regs1 n i mp L) HS2 HAE4 E41 Hret HJ0 HJ2 Hwlo Hwhi UN4 HGc4)
  | _ => idtac end.
(* BACK: one more request; +0xb0 again with i + 1 *)
all: paj_run_to_tok RUNTO HS2 HJ2 SHOK2 Bspan (AF_check_requests + 0xb0); [lf_awr |].
all: rq_nokept HFr W UF4; pose proof (rq_grow _ _ _ HG) as GR4; clear HF HFr HG.
all: lazymatch type of HS2 with st_ok_pi _ _ ?EV ?ssF (restrict _ ?msF) =>
       rename msF into msB; set (E4 := EV) in *; set (ssB := ssF) in HS2 end.
all: assert (EW4 : forall a, (a < 64)%nat -> ew E4 a = ew E a)
  by (intros a Ha; unfold E4; rewrite ?ew_ewset_other by lia; apply EW3; exact Ha).
all: assert (Y32 : ew E4 32 = Z_to_bv 64 SB) by (rewrite EW4 by lia; exact XX32).
all: assert (Y33 : ew E4 33 = Z_to_bv 64 (n - i)) by (rewrite EW4 by lia; exact XX33).
all: assert (Y34 : ew E4 34 = Z_to_bv 64 (RQ_SL + 8 * i)) by (rewrite EW4 by lia; exact XX34).
all: assert (Y35 : ew E4 35 = Z_to_bv 64 (mp + MD_REQ_LEN + 8 * i)) by (rewrite EW4 by lia; exact XX35).
all: assert (Y36 : ew E4 36 = Z_to_bv 64 (RQ_SD + 512 * i)) by (rewrite EW4 by lia; exact XX36).
all: assert (Y37 : ew E4 37 = Z_to_bv 64 (mp + MD_REQ + 512 * i)) by (rewrite EW4 by lia; exact XX37).
all: assert (BREG : forall r : bv 5, getr (ms_regs msB) r = sv_denot E4 (sr_get (ss_regs ssB) r))
  by (intros r; exact (st_ok_pi_restrict_reg (w_H W) E4 ssB msB r HS2)).
all: assert (HINVB : rq_inv regs (ms_regs msB) n (i + 1) mp);
  [ unfold rq_inv; rewrite !BREG; unfold ssB;
    repeat split;
    lazymatch goal with |- sv_denot _ (sr_get ?LL ?RR) = _ =>
      let v := eval vm_compute in (sr_get LL RR) in change (sr_get LL RR) with v end;
    first
    [ rewrite (rq_soffc E4 2 (-80) (spZ regs)); [reflexivity | rewrite EW4 by lia; rewrite EE2;
        symmetry; apply Z_to_bv_bv_unsigned | lia]
    | rewrite rq_soff0, EW4 by lia; first [exact EE3 | exact EE4 | exact XX32
        | apply (rq_E_reg _ _ _ _ _ _ 25%nat 25%bv); [reflexivity | lia]
        | apply (rq_E_reg _ _ _ _ _ _ 26%nat 26%bv); [reflexivity | lia]
        | apply (rq_E_reg _ _ _ _ _ _ 27%nat 27%bv); [reflexivity | lia] ]
    | rewrite (rq_soffc E4 37 512 (mp + MD_REQ + 512 * i) Y37) by lia; f_equal; lia
    | rewrite (rq_soffc E4 36 512 (RQ_SD + 512 * i) Y36) by lia; f_equal; lia
    | rewrite (rq_soffc E4 35 8 (mp + MD_REQ_LEN + 8 * i) Y35) by lia; f_equal; lia
    | rewrite (rq_soffc E4 34 8 (RQ_SL + 8 * i) Y34) by lia; f_equal; lia
    | rewrite (rq_soffc E4 33 (-1) (n - i) Y33) by lia; f_equal; lia
    | rewrite (rq_denot_shx1 E4 (RQ_SL + 8 * i) SB Y34 Y32) by lia; f_equal;
      replace (RQ_SL + 8 * (i + 1)) with ((RQ_SL + 8 * i) + 1 * 8) by lia;
      rewrite Z_div_plus_full by lia; lia ] | ].
all: assert (HSVB : rq_saved W (ms_mem msB) regs);
  [ unfold rq_saved in HSV |- *;
    destruct HSV as (S8 & S7 & S6 & S5 & S4 & S3 & S2 & S1 & S0 & SRA);
    repeat split;
    (eapply rq_val_frame; [eassumption | intros x Hx; apply (mbyte_of_aview SEGS);
       rewrite (UF4 x ltac:(lia) ltac:(intros [])); apply FRC; lia]) | ].
all: assert (UNB : forall a, 0 <= a < 2 ^ 64 -> ~ lf_Zs 8272 (spZ regs) a ->
              aview SEGS (w_H W) (ms_mem msB) a = aview SEGS (w_H W) memc a)
  by (intros a Ha Hw; rewrite (UF4 a Ha ltac:(intros [])); exact (UN3 a Ha Hw)).
all: assert (HGcB : mem_grows (rdW W memc) (rdW W (ms_mem msB)))
  by (apply rq_grows_of_present; intros a Ha; apply GR4; exact (rq_grow _ _ _ HGc3 a Ha)).
all: pmkst HS2.
all: lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?pcl)) _ _) _) _ =>
       replace pcl with (AF_check_requests + 0xb0) by (vm_compute; reflexivity) end.
all: apply (IH (i + 1) (ms_mem msB) _ (ms_regs msB));
  [ lia | lia | lia | exact HJ2 | exact UNB | exact HGcB
  | repeat rewrite (proj1 (wvb_fds_fs _ _ _)); rewrite (same_but_materialized_wvb _ _ Hsm);
    repeat rewrite (proj1 (wvb_fds_fs _ _ _)); exact Hfd1
  | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); rewrite (same_but_materialized_wvb _ _ Hsm);
    repeat rewrite (proj2 (wvb_fds_fs _ _ _)); exact Hfs1
  | exact HINVB | exact HSVB ].
Qed.


Lemma rq_region : forall E ss ms i r,
  st_ok_pi SEGS VAL E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok SEGS E (ms_mem ms) r.
Proof. intros E ss ms i r HS Hi. exact (st_ok_region_nth (segs := SEGS) E (abs_ss VAL ss) ms i r HS Hi). Qed.

(* a byte the runtime owns is no byte of a read set *)
Lemma rq_owned_not_akb : forall lyc Sc (W : world SEGS) memc mdc slo shi a,
  AR SEGS B lyc Sc W memc mdc -> aowned B lyc Sc a -> ~ akb SEGS B lyc Sc slo shi a.
Proof.
intros lyc Sc W memc mdc slo shi a HAR Ho [H|[H|[H|H]]].
- exact (al_stack _ _ LAWS lyc Sc W memc mdc a HAR (proj1 H) Ho).
- destruct H as (b & m & Hin & Hb).
  destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hin) as (_ & _ & _ & _ & Hk & _).
  exact (proj2 (Hk a Hb) Ho).
- destruct H as (Hi & Hno & _). apply Hno. exact (proj1 (al_owned_image _ _ LAWS lyc Sc W memc mdc a HAR Hi) Ho).
- destruct H as (cid & pos & Hin & Hr).
  destruct (al_frames _ _ LAWS lyc Sc W memc mdc cid pos HAR Hin) as (_ & _ & Hf & _).
  unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr. exact (proj2 (Hf a ltac:(lia)) Ho).
Qed.

(* a read-set range misses each of the runtime's own areas (the .got word, the shadow-base cell, ...) *)
Lemma rq_apart_area : forall lyc Sc (W : world SEGS) memc mdc slo shi p n r,
  AR SEGS B lyc Sc W memc mdc -> In r (asyms_areas B) -> 0 < snd r -> 0 < n ->
  (forall a, p <= a < p + n -> akb SEGS B lyc Sc slo shi a) ->
  p + n <= fst r \/ fst r + snd r <= p.
Proof.
intros lyc Sc W memc mdc slo shi p n r HAR Hr Hr0 Hn Hk.
destruct (Z_le_gt_dec (p + n) (fst r)) as [H1|H1]; [left; exact H1|].
destruct (Z_le_gt_dec (fst r + snd r) p) as [H2|H2]; [right; exact H2|].
exfalso. apply (rq_owned_not_akb lyc Sc W memc mdc slo shi (Z.max p (fst r)) HAR).
- eapply YG0q.own_area; [exact (proj1 HAR) | exact Hr | lia].
- apply Hk. lia.
Qed.

Lemma rq_vals : VAL (A_OBJ 1) = 0xa19d0 /\ VAL (A_OBJ 2) = LA_G_NL /\ VAL (A_OBJ 64) = 0xaa438 /\ BASE = 0x821cc.
Proof.
  split; [rewrite (lv_obj LV 1) by (unfold link_nobj; lia); reflexivity|].
  split; [rewrite (lv_obj LV 2) by (unfold link_nobj; lia); reflexivity|].
  split; [rewrite (lv_obj LV 64) by (unfold link_nobj; lia); reflexivity|].
  exact (lv_text LV).
Qed.

(* THE ENTRY STATE *)
Lemma rq_entry : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) kbs mbs,
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - 8272 -> spZ regs <= sp0 ->
  (forall a, aarg regs 0 <= a < aarg regs 0 + MD_SIZE -> akb SEGS B lyc Sc (spZ regs - 8272) (spZ regs) a) ->
  anlk_at SEGS (rdW W memc) LA_G_NL kbs -> amodel_at SEGS (rdW W memc) (aarg regs 0) mbs ->
  nlk_wf kbs -> requests_are kbs mbs -> amem_range (aarg regs 0) MD_SIZE ->
  apart_frame regs 8272 (aarg regs 0) MD_SIZE -> apart_gnl LA_G_NL (aarg regs 0) MD_SIZE ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs (rq_eextra (nk_n_sent kbs)))) rq_ss
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_check_requests)) memc (seg_rom SEGS))).
Proof.
intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs kbs mbs HJ H16 Hwlo Hwhi HRd HNK HMD WF HRQ
  AMR HAPF HAPG.
pose proof HJ as (HSTK & HXO & (memS & HJi & _) & _).
pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & _ & Kgot & _).
pose proof (pal_got_shadow B TL) as PG. pose proof (pal_cell B TL) as PC.
rewrite PG in Kgot. rewrite PC in Kgot, Kcell.
destruct rq_vals as (V1 & V2 & V64 & VB).
rewrite V1, V64 in Kgot. rewrite V64 in Kcell. rewrite V1 in PG. rewrite V64 in PC.
unfold apart_frame, apart_gnl in HAPF, HAPG.
pose proof WF as (_ & _ & Wns & _). unfold NL_SENT_MAX in Wns.
destruct HRQ as (Heqn & _).
set (n := nk_n_sent kbs) in *. set (mp := aarg regs 0) in *.
assert (HMD1 : MD_SIZE = 8856) by reflexivity. assert (HNKs : NK_SIZE = 271992) by reflexivity.
assert (HGb : LA_G_NL = 6146752) by reflexivity. assert (HSBb : SB = 2147450880) by reflexivity.
assert (Hmp : 0 <= mp /\ mp + MD_SIZE <= 2 ^ 47 - 1).
{ split.
  - unfold mp, aarg, argZ. apply bv_unsigned_in_range.
  - unfold amem_range in AMR. unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in AMR. rewrite HMD1 in *. lia. }
(* the model block misses the .got word and the shadow-base cell *)
assert (Dgot : mp + MD_SIZE <= 0xa19d0 \/ 0xa19d0 + 8 <= mp).
{ rewrite <- PG. refine (rq_apart_area lyc Sc W memc mdc _ _ mp MD_SIZE (as_got_shadow B, 8) HAR _ ltac:(cbn; lia)
    ltac:(lia) HRd). unfold asyms_areas. cbn [In]. tauto. }
assert (Dcell : mp + MD_SIZE <= 0xaa438 \/ 0xaa438 + 8 <= mp).
{ rewrite <- PC. refine (rq_apart_area lyc Sc W memc mdc _ _ mp MD_SIZE (as_shadow_cell B, 8) HAR _ ltac:(cbn; lia)
    ltac:(lia) HRd). unfold asyms_areas. cbn [In]. tauto. }
set (E := Eimg (Ereg regs (rq_eextra n))).
assert (EL : forall m, (m < A_TEXT)%nat -> ew E m = ew (Ereg regs (rq_eextra n)) m)
  by (intros m Hm; apply Eimg_low; exact Hm).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = getr regs 10) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 10 10%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 n) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (Eg : ew E (A_OBJ 2) = Z_to_bv 64 LA_G_NL)
  by (unfold E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); rewrite V2; reflexivity).
assert (Egot : ew E (A_OBJ 1) = Z_to_bv 64 0xa19d0)
  by (unfold E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); rewrite V1; reflexivity).
assert (Ecell : ew E (A_OBJ 64) = Z_to_bv 64 0xaa438)
  by (unfold E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); rewrite V64; reflexivity).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (U10 : bv_unsigned (ew E 10) = mp) by (rewrite E10; reflexivity).
assert (VBv : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v).
{ intros m v Hm Hv. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv. }
rewrite restrict_mkst_fx. unfold rq_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold rq_regions, stack_region, got_regionP, bcell_regionP, rq_ns, rq_nr.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. fold E. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + fold E. rewrite (VBv _ _ Egot) by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ 0xa19d0 0 8 (SOff (A_OBJ 64) 0) 0xaa438);
      [cbn [sv_denot]; rewrite Ecell, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zrng | zrng |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot).
  + fold E. rewrite (VBv _ _ Ecell) by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ 0xaa438 0 8 (SOff 32 0) SB);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zrng | zrng |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
  + fold E. rewrite (VBv _ _ Eg) by lia.
    split; [unfold NK_N_SENT; lia|]. split; [unfold NK_N_SENT; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ LA_G_NL NK_N_SENT 4 (SOff 33 0) n);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zrng | zrng |].
    exact (anlk_field SEGS (rdW W memc) LA_G_NL kbs NK_N_SENT 4 HNK ltac:(unfold NK_N_SENT; lia)
             ltac:(unfold NK_N_SENT; lia)).
  + cbn [base_val]. fold E. rewrite U10.
    split; [unfold MD_N_REQ; lia|]. split; [unfold MD_N_REQ; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ mp MD_N_REQ 4 (SOff 33 0) n);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zrng | zrng |].
    destruct HMD as [[Hab _] HmL]. rewrite Heqn.
    exact (val_mem_of_abytes SEGS (rdW W memc) mp mbs MD_N_REQ 4 Hab ltac:(unfold MD_N_REQ; lia)
             ltac:(unfold MD_N_REQ; lia)).
- apply pairwise_disjoint_of_extents.
  unfold rq_regions, stack_region, got_regionP, bcell_regionP, rq_ns, rq_nr, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  fold E. rewrite (VBv _ _ Egot), (VBv _ _ Ecell), (VBv _ _ Eg) by lia.
  cbn [base_val]. rewrite Usp, U10.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold NK_N_SENT, MD_N_REQ.
  repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [rq_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  fold E. rewrite Usp, E32, E33, Eg, U10.
  rewrite !unsigned_lit_small by lia.
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.

Theorem check_requests_aproof : forall rlo rhi, check_requests_acontract SK SEGS rlo rhi B.
Proof.
intros rlo rhi. unfold check_requests_acontract, aleaf_rd, check_requests_apost, check_requests_awr.
intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HA HRd HPre.
destruct HA as (HJ & HGX & HROD & Hret & Hra4 & Hgp & Htp & H16 & Hwlo & Hwhi & Hev & Hside & Hajw & _).
destruct HPre as (kbs & mbs & HNK & HMD & WF & MWF & HRQ & RAM & HUM & AMR & RAG & HUG & HAPF & HAPG).
change CHECK_REQUESTS_AK with 8272 in *.
unfold check_requests_ard, rd_ivl in HRd.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
pose proof HJ as HJ0.
pose proof HJ as (HSTK & HXO & (memS & HJi & _) & _).
pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
destruct rq_vals as (V1 & V2 & V64 & VB).
pose proof (rq_entry G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs kbs mbs HJ H16 Hwlo Hwhi
  ltac:(intros a Ha; apply HRd; lia) HNK HMD WF HRQ AMR HAPF HAPG) as HS.
replace (cfg_at SEGS CHECK_REQUESTS_A regs memc mdc)
  with (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_check_requests)) memc (seg_rom SEGS)) mdc)
  by (unfold cfg_at, w64, CHECK_REQUESTS_A, AF_check_requests; rewrite VB; reflexivity).
pose proof WF as (_ & _ & Wns & _). unfold NL_SENT_MAX in Wns.
set (n := nk_n_sent kbs) in *. set (mp := aarg regs 0) in *.
assert (HMD1 : MD_SIZE = 8856) by reflexivity. assert (HNKs : NK_SIZE = 271992) by reflexivity.
assert (HGb : LA_G_NL = 6146752) by reflexivity. assert (HSBb : SB = 2147450880) by reflexivity.
assert (Hmp : 0 <= mp /\ mp + MD_SIZE <= 2 ^ 47 - 1).
{ split.
  - unfold mp, aarg, argZ. apply bv_unsigned_in_range.
  - unfold amem_range in AMR. unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in AMR. rewrite HMD1 in *. lia. }
remember (Eimg (Ereg regs (rq_eextra n))) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall m, (m < A_TEXT)%nat -> ew E m = ew (Ereg regs (rq_eextra n)) m)
  by (intros m Hm; subst E; apply Eimg_low; exact Hm).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = getr regs 10) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 10 10%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 n) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (ERg : forall (m : nat) (r : bv 5), Z.of_nat m = bv_unsigned r -> (m < 32)%nat -> ew E m = getr regs r)
  by (intros m r Hm Hl; rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
assert (Eg : ew E 243 = Z_to_bv 64 LA_G_NL)
  by (subst E; change 243%nat with (A_OBJ 2); rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); rewrite V2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (rq_eextra n)) E)
  by (split; [intros m Hm; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (U10 : bv_unsigned (ew E 10) = mp) by (rewrite E10; reflexivity).
clear HEdef EL.
assert (SHOK : sh_ok SEGS (SOff 32 0) rq_SH E (mrestrict (w_H W) memc)).
{ unfold rq_SH. apply Forall_cons; [|apply Forall_nil]. unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
  rewrite (U_atom E 32 SB E32) by lia. rewrite (U_atom E 10 mp ltac:(rewrite E10; unfold w64; symmetry; apply Z_to_bv_bv_unsigned)) by lia.
  rewrite ?Z.add_0_r, ?Z.sub_0_r. split.
  - rewrite <- (aview_rd_of SEGS). change SB with SHADOW_OFF. intros x Hx. apply RAM. unfold MD_N_REQ in *. lia.
  - intros a Ha. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, MD_N_REQ in *. lia. }
assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ lf_Zs 8272 (spZ regs) a ->
          aview SEGS (w_H W) memc a = aview SEGS (w_H W) memc a) by reflexivity.
assert (HGc : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) memc)) by apply mem_grows_refl.
pose proof (paj_run_x SK B LAWS G HGX XO OUT) as RUN.
pose proof (paj_run_to_x SK B LAWS G HGX XO OUT) as RUNTO.
pose proof (paj_branch (PI := PI)) as BR.
(* +0x00 .. +0x70: the frame, the shadow base, n_sent, the check of n_req and the load, `bne` (decided), `blez` *)
paj_run_tok RUN HS HJ SHOK Bspan; [lf_awr |].
lf_kept HFr W 8272 (spZ regs) UNk. clear HF HFr. lf_fold UN HGc UNk HG W memc 8272 (spZ regs).
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* n = 0: +0x114 .. +0x140 restore, pop, ret *)
  paj_run_tok RUN HS HJ SHOK Bspan; [lf_awr |].
  lf_kept HFr W 8272 (spZ regs) UNk. clear HF HFr. lf_fold UN HGc UNk HG W memc 8272 (spZ regs).
  lazymatch type of HS with st_ok_pi _ _ ?Ef _ _ =>
    assert (HAEf : env_agree 32 (Ereg regs (rq_eextra n)) Ef)
      by (split; [intros nn Hnn; rewrite ?ew_ewset_other by lia; exact (proj1 HAE nn Hnn) | exact (proj2 HAE)]);
    assert (E1f : ew Ef 1 = getr regs 1) by (rewrite ?ew_ewset_other by lia; exact E1)
  end.
  lf_ret PI LAWS W regs (rq_eextra n) HS HAEf E1 Hret HJ0 HJ Hwlo Hwhi UN HGc.
- (* n > 0: +0x74 .. +0xac set the cursors; the loop at +0xb0 *)
  assert (Hnpos : 0 < n).
  { destruct (Z.eq_dec n 0) as [Hn0|Hn0]; [|lia]. exfalso.
    rewrite rq_soff0 in Hc. rewrite ?ew_ewset_other in Hc by lia. rewrite E33, Hn0 in Hc. vm_compute in Hc. discriminate. }
  paj_run_to_tok RUNTO HS HJ SHOK Bspan (AF_check_requests + 0xb0); [lf_awr |].
  lf_kept HFr W 8272 (spZ regs) UNk. clear HF HFr. lf_fold UN HGc UNk HG W memc 8272 (spZ regs).
  lazymatch type of HS with st_ok_pi _ _ ?EV ?ssF (restrict _ ?msF) =>
    rename msF into ms1; set (E1v := EV) in *; set (ss1 := ssF) in HS end.
  assert (EW : forall a, (a < 512)%nat -> ew E1v a = ew E a)
    by (intros a Ha; unfold E1v; rewrite ?ew_ewset_other by lia; reflexivity).
  assert (BREG : forall r : bv 5, getr (ms_regs ms1) r = sv_denot E1v (sr_get (ss_regs ss1) r))
    by (intros r; exact (st_ok_pi_restrict_reg (w_H W) E1v ss1 ms1 r HS)).
  assert (HINV : rq_inv regs (ms_regs ms1) n 0 mp).
  { assert (W10 : ew E1v 10 = Z_to_bv 64 mp)
      by ((rewrite EW by lia); rewrite E10; unfold mp, aarg, argZ; symmetry; apply Z_to_bv_bv_unsigned).
    assert (W243 : ew E1v 243 = Z_to_bv 64 LA_G_NL) by ((rewrite EW by lia); exact Eg).
    assert (W33 : ew E1v 33 = Z_to_bv 64 n) by ((rewrite EW by lia); exact E33).
    assert (W32 : ew E1v 32 = Z_to_bv 64 SB) by ((rewrite EW by lia); exact E32).
    assert (W2 : ew E1v 2 = Z_to_bv 64 (spZ regs)) by ((rewrite EW by lia); rewrite E2; symmetry; apply Z_to_bv_bv_unsigned).
    unfold rq_inv; rewrite !BREG; unfold ss1.
    repeat split;
    lazymatch goal with |- sv_denot _ (sr_get ?LL ?RR) = _ =>
      let v := eval vm_compute in (sr_get LL RR) in change (sr_get LL RR) with v end;
    first
    [ rewrite (rq_soffc E1v 2 (-80) (spZ regs) W2) by lia; reflexivity
    | rewrite rq_soff0; (rewrite EW by lia); first [exact E3 | exact E4 | exact E32
        | apply ERg; [reflexivity | lia] ]
    | rewrite (rq_soffc E1v 10 _ mp W10) by lia; f_equal; unfold MD_REQ, MD_REQ_LEN; lia
    | rewrite (rq_soffc E1v 243 _ LA_G_NL W243) by lia; f_equal; unfold RQ_SD, RQ_SL, NK_SENT, NK_SENT_LEN; lia
    | rewrite (rq_soffc E1v 33 0 n W33) by lia; f_equal; lia
    | rewrite (rq_denot_shx_g E1v 243 270888 LA_G_NL SB W243 W32) by lia; f_equal; unfold RQ_SL, NK_SENT_LEN; lia ]. }
  assert (HSV : rq_saved W (ms_mem ms1) regs).
  { pose proof (rq_region _ _ _ 0 _ HS eq_refl) as HR. unfold ss1 in HR. cbn [ss_mem nth_error ms_mem restrict] in HR.
    unfold rq_saved.
    repeat split;
    (eapply (field_of_region (segs := SEGS) _ _ _ _ _ _ _ _ _ _ 8%N);
       [ exact HR
       | (rewrite EW by lia); exact Usp
       | repeat (first [left; reflexivity | right])
       | rewrite rq_soff0; (rewrite EW by lia); rewrite Z_to_bv_bv_unsigned; apply ERg; [reflexivity | lia]
       | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply bv_unsigned_in_range
       | cbn; lia ]). }
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?pcl)) _ _) _) _ =>
    replace pcl with (AF_check_requests + 0xb0) by (vm_compute; reflexivity) end.
  apply (rq_loop G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs kbs mbs HGX HJ0 Hret Hgp Htp
           H16 Hwlo Hwhi HNK HMD WF HRQ RAM HUM AMR RAG HUG HAPF HAPG (Z.to_nat (n - 0)) 0 (ms_mem ms1) _ (ms_regs ms1));
    [ reflexivity | lia | lia
    | first [exact HJ | rewrite wvb_collapse in HJ; exact HJ | apply (ajournal_gx_materialize SEGS B LAWS pa_segs_low); exact HJ]
    | exact UN | exact HGc
    | repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity
    | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity
    | exact HINV | exact HSV ].
Qed.
End w.

(* LAWS and BCMP discharged on the image's segments: lib/Reusable/YG0q.v AR_laws_ok and lib/A/AE2s.v
   bcmp_icpt_contract, from the image's asyms record (lib/A/AF0m.v PcapSyms; on the image lib/A/AD2l.v PcapB_syms) *)
Section img. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
Context {PI : PAImg link_listing}.
Theorem check_requests_aproof_img : forall B, PALib B -> LinkVals -> AF0m.PcapSyms B -> pa_segs = AB1v.tfibsegs ->
  forall rlo rhi, check_requests_acontract SK pa_segs rlo rhi B.
Proof.
intros B TL LV TS Hsegs.
assert (LAWS : AR_laws pa_segs B) by (rewrite Hsegs; exact (YG0q.AR_laws_ok AB1v.tfibsegs B)).
apply (check_requests_aproof SK B LAWS TL LV).
rewrite (lv_sigma LV). cbn [link_sigma]. rewrite Hsegs.
exact (AE2s.bcmp_icpt_contract B (YG0q.AR_laws_ok AB1v.tfibsegs B) TS).
Qed.
End img.

Print Assumptions check_requests_aproof.
Print Assumptions check_requests_aproof_img.
