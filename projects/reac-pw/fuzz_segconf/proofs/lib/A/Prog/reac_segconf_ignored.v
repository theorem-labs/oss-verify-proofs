(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of sup_reply_code (plugin-hostd/fuzz_command, 0x89d6c, 20 instructions), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (pb_cmpPixel, a leaf that ends in a tail jump to a runtime entry) and A/ACh2.v (the step through a call and back). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/sup_reply_code.v, with its module paths and module names changed; 422 of its 488 lines of code are new or changed and 222 lines of the source are left out. *)
(* The ASan walk of reac_segconf_ignored on fuzz_segconf image A (fuzz_segconf.asan 0x89594 = BASE +
   AF_reac_segconf_ignored, 23 instructions): reac_segconf_ignored_contract (reac_segconf_ignored_c.v) at image A's
   numbers, from reac_segconf_find_contract at find's entry (the Section hypothesis FIND). Step plan:
   provenance/evidence/listing-plans/plan-reac_segconf_ignored.md.
   Form: plugin-hostd/fuzz_command's lib/A/Prog/check_refusal.v and check_refusal_s1.v (the entry state, a program
   call through cl_callS, the branches, the return) and arg_line.v (after a call: the shadow entry and a region of
   the returned pointer). Control flow: the plain / UBSan owner's plain walk lib/Prog/reac_segconf_ignored.v.
   - 0x89594-0x895a8: the 16-byte frame (ra, s0 saved), the shadow base through the GOT word A_OBJ 0 into s0.
   - 0x895ac: jal reac_segconf_find, a0 = c and a1 = name as at the entry; s0 = 0x7fff8000 is below alloc_ceiling, so
     the frame chain the callee asks is the empty one.
   - 0x895b0: beqz a0. Taken (find_ptr = 0, so r_find = None): the epilogue returns 0. Not taken: a0 = c + 356 i
     with r_find = Some i; the instrumented check of the 4-byte load at a0 + 24 passes by the shadow of c's heap
     block at the state after the call (AR_shadow_law: the block is live there, find allocates nothing); the load
     gives the ignore flag (0 or 1), snez keeps it; the epilogue returns it.
   - the post's sa_kept: the frame stores lie in [sp - 16, sp), find's sa_kept covers its own window below it, the
     instructions after the call store nothing.
   Image A's numbers are SegInstA's: STK_reac_segconf_ignored, STK_reac_segconf_find, RLO_A, RHI_A. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaDenot PaSB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec seg_query_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import reac_segconf_find_c reac_segconf_ignored_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* image A's stacks (SegInstA), unfolded *)
Ltac ri_stk := unfold SegInstA.STK_reac_segconf_ignored, SegInstA.STK_reac_segconf_find, ESTACK in *.

(* the symbolic entry state: atom 32 the shadow base; the frame, the GOT word of the shadow-base cell (A_OBJ 0) and the
   cell (A_OBJ 12) *)
Definition RI_SB : Z := 0x7fff8000.
Definition RIx : sv := SOff 32 0.
Definition RIspan : Z * Z := (RI_SB, RI_SB + 2 ^ 44 - 1).
Definition ri_regions : smem := [stack_region 16; got_regionP; bcell_regionP 32].
Definition ri_facts : facts := mkFacts [(2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF RI_SB RI_SB 0)] [] [].
Definition ss_ri : sstate := mkSS AF_reac_segconf_ignored sr_atoms ri_regions None ri_facts.
Definition ri_extra : list word := [Z_to_bv 64 RI_SB].
(* after the call (atoms 40.. the clobbered registers, a0 = atom 44), on the found arm: the ignore field at a0 + 24
   holding v, its shadow entry, and the fact on the pointer *)
Definition ri_field (v : Z) : YP09.region := YP09.mkRegion (Some 44%nat) 24 28 0 0 [YP09.mkChunk 24 (CVal 4 (SLit v))].
Definition ri_SH : list shent := [mkSHE 44 24 28].
Definition ri_pfact : afact := mkAF 4096 0x7fffff800000 2.

(* ------------------------------ reads that agree below a bound ------------------------------ *)
Definition ri_low (lim : Z) (rd rd' : reader) : Prop := forall a, 0 <= a < lim -> rd' a = rd a.
Lemma ri_bytes_low : forall lim rd rd' a bs, ri_low lim rd rd' -> 0 <= a -> a + Z.of_nat (length bs) <= lim ->
  sa_bytes rd a bs -> sa_bytes rd' a bs.
Proof. intros lim rd rd' a bs HK H0 H1 H i Hi. rewrite HK by lia. exact (H i Hi). Qed.
Lemma ri_str_low : forall lim rd rd' p s, ri_low lim rd rd' -> 0 <= p ->
  (p + Z.of_nat (length s)) - (p + Z.of_nat (length s)) mod 8 + 8 <= lim -> p + Z.of_nat (length s) + 1 <= lim ->
  sa_str rd p s -> sa_str rd' p s.
Proof.
intros lim rd rd' p s HK H0 Ht Hl ((Hz & Hn) & Htl). split; [split; [|exact Hn]|].
- intros i Hi. pose proof Hi as Hi'. rewrite length_app in Hi'. cbn [length] in Hi'.
  rewrite HK by lia. exact (Hz i Hi).
- intros x Hx. pose proof (Z.mod_pos_bound (p + Z.of_nat (length s)) 8 ltac:(lia)). rewrite HK by lia. exact (Htl x Hx).
Qed.
Lemma ri_ra_low : forall lim rd rd' q n, ri_low lim rd rd' -> 0 <= q -> q + n <= 2 ^ 47 -> SHADOW_OFF + 2 ^ 44 + 16 <= lim ->
  range_addressable rd SHADOW_OFF q n -> range_addressable rd' SHADOW_OFF q n.
Proof.
intros lim rd rd' q n HK H0 H1 Hl H x Hx. destruct (H x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
rewrite HK; [exact Hs|]. unfold shadow_of_addr.
assert (A1 : 0 <= x / 8) by (apply Z.div_pos; lia).
assert (A2 : x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
unfold SHADOW_OFF in *. lia.
Qed.
Lemma ri_hull_low : forall lim rd rd' q n, ri_low lim rd rd' -> 0 <= q -> 0 < n -> q + n <= 2 ^ 47 ->
  SHADOW_OFF + 2 ^ 44 + 16 <= lim -> shadow_hull_vis rd q n -> shadow_hull_vis rd' q n.
Proof.
intros lim rd rd' q n HK H0 Hn H1 Hl H s Hs. pose proof Hs as Hs'. unfold shadow_addr in Hs'.
assert (A1 : 0 <= q / 8) by (apply Z.div_pos; lia).
assert (A2 : (q + n - 1) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
assert (A3 : 0 <= (SHADOW_OFF + q / 8) / 8 * 8) by (apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; unfold SHADOW_OFF; lia).
assert (A4 : (SHADOW_OFF + (q + n - 1) / 8) / 8 * 8 <= SHADOW_OFF + (q + n - 1) / 8)
  by (rewrite Z.mul_comm; apply Z.mul_div_le; lia).
rewrite HK; [exact (H s Hs)|]. unfold SHADOW_OFF in *. lia.
Qed.
Lemma ri_addr_low : forall lim rd rd' q n, ri_low lim rd rd' -> q + n <= 2 ^ 47 -> SHADOW_OFF + 2 ^ 44 + 16 <= lim ->
  sa_addr rd q n -> sa_addr rd' q n.
Proof.
intros lim rd rd' q n HK H1 Hl (H0 & H63 & Hm & Hra & Hh).
split; [exact H0|]. split; [exact H63|]. split; [exact Hm|]. split.
- exact (ri_ra_low lim rd rd' q n HK H0 H1 Hl Hra).
- intros Hn. exact (ri_hull_low lim rd rd' q n HK H0 Hn H1 Hl (Hh Hn)).
Qed.
(* an n-wide field read through a view is the same field of the restricted memory (check_refusal_s1.v
   cr_val_of_aval, over SegABase's sa_val) *)
Lemma ri_val_of_sa : forall segs H (mem : word -> option byte) a n v,
  sa_val (aview segs H mem) a n v -> val_mem segs (mrestrict H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte segs (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Eb; cbn in Hv; [|discriminate Hv].
injection Hv as Hb. rewrite <- (Z_to_bv_bv_unsigned 8 b). rewrite Hb. reflexivity.
Qed.

(* ------------------------------ the ignore field of c->seg[i] ------------------------------ *)
Lemma ri_nth_skipn : forall {A} (l : list A) a k d, nth k (skipn a l) d = nth (a + k) l d.
Proof.
intros A l a. revert l. induction a as [|a IH]; intros l k d; [reflexivity|].
destruct l as [|x l]; cbn [skipn].
- destruct k; reflexivity.
- cbn [Nat.add nth]. apply IH.
Qed.
Lemma ri_nth_firstn : forall {A} (l : list A) n k d, (k < n)%nat -> nth k (firstn n l) d = nth k l d.
Proof.
intros A l. induction l as [|x l IH]; intros n k d Hk.
- destruct n; cbn [firstn]; reflexivity.
- destruct n as [|n]; [lia|]. cbn [firstn]. destruct k as [|k]; [reflexivity|]. cbn [nth]. apply IH. lia.
Qed.
Lemma ri_ignore_val : forall rd c bs rcs i, sa_bytes rd c bs -> seg_spec.rconf_enc rcs bs ->
  (i < length (rc_seg rcs))%nat ->
  sa_val rd (c + 356 * Z.of_nat i + 24) 4 (seg_spec.b2z (rs_ignore (r_seg rcs i))).
Proof.
intros rd c bs rcs i HB HE Hi.
pose proof HE as (HL & HLS & HSEG & _).
pose proof (HSEG i Hi) as (_ & _ & _ & _ & HIG & _).
unfold seg_spec.SEG_C_SIZE in HL.
intros k Hk.
replace (c + 356 * Z.of_nat i + 24 + Z.of_nat k) with (c + Z.of_nat (356 * i + 24 + k)) by lia.
rewrite (HB (356 * i + 24 + k)%nat) by lia.
assert (HN : nth (356 * i + 24 + k) bs ZB0 =
  nth k (seg_spec.fldz seg_spec.RS_IGNORE 4 (seg_spec.fld (356 * i) 356 bs)) ZB0).
{ unfold seg_spec.fldz, seg_spec.fld, seg_spec.RS_IGNORE. change (Z.to_nat 24) with 24%nat. change (Z.to_nat 4) with 4%nat.
  rewrite ri_nth_firstn by lia. rewrite ri_nth_skipn. rewrite ri_nth_firstn by lia. rewrite ri_nth_skipn.
  f_equal. lia. }
rewrite HN. unfold seg_spec.flag_enc in HIG. rewrite HIG. unfold seg_spec.b2z.
unfold r_seg. destruct (rs_ignore (nth i (rc_seg rcs) rseg_d)); (do 4 (destruct k as [|k]; [reflexivity|])); lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Definition ri_E (regs : bvmap 5 word) : env := Eimg (Ereg regs ri_extra).
Lemma ri_ew_img : forall E a, img_env VAL A_LIM E -> (A_TEXT <= a < A_LIM)%nat -> ew E a = Z_to_bv 64 (VAL a).
Proof using.
intros E a HE Ha. apply bv_eq. rewrite (HE a Ha). rewrite unsigned_lit_small; [reflexivity|]. exact (pa_val_range a).
Qed.
Section e.
Variable B : asyms.
Hypothesis FIND : reac_segconf_find_contract SEGS B (BASE + AF_reac_segconf_find) SegInstA.STK_reac_segconf_find SegInstA.RLO_A SegInstA.RHI_A.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis SIGP : seg_sig_prog.

(* where the reader's block and the name end: below alloc_ceiling *)
Lemma ri_loc_end : forall ly S (W : world SEGS) mem md q n, AR SEGS B ly S W mem md -> 0 < n ->
  sa_loc SEGS B ly S q n -> 0 <= q /\ q + n <= alloc_ceiling.
Proof using LAWS.
intros ly S W mem md q n HAR Hn [(b & m & Hbm & Hb & Hq) | [(cid & pos & Hin & Hcid & Hf1 & Hf2) | Himg]].
- destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hbm) as (_ & Hb4096 & Hbceil & _).
  pose proof (req_size_pos m) as Hreq. unfold req_size in *. destruct (Z.eqb_spec m 0); lia.
- destruct (al_sep _ _ LAWS ly S W mem md HAR) as [_ HF].
  rewrite Forall_forall in HF. specialize (HF (cid, pos) Hin). cbn [fst snd] in HF. lia.
- destruct (Himg q ltac:(lia)) as (Hi1 & _). destruct (Himg (q + n - 1) ltac:(lia)) as (Hi2 & _).
  pose proof (pa_img_range q Hi1). pose proof (pa_img_range (q + n - 1) Hi2).
  pose proof asan_consts as (C1 & _). unfold kImgEnd in *. lia.
Qed.

(* query_pre of a reader that agrees with the entry's below alloc_ceiling *)
Lemma ri_qp_low : forall ly S (W : world SEGS) mem md (rd' : reader) c name rcs nm,
  AR SEGS B ly S W mem md -> ri_low alloc_ceiling (rdW W mem) rd' ->
  query_pre SEGS B ly S (rdW W mem) c name rcs nm -> query_pre SEGS B ly S rd' c name rcs nm.
Proof using LAWS.
intros ly S W mem md rd' c name rcs nm HAR HK
  (Hc0 & Hc16 & (bs & HB & HE) & Hheap & Haddr & Hn0 & Hstr & Hloc & Haddrn & Hlen).
pose proof asan_consts as (C1 & _). pose proof alloc_ceiling_lt as HAC47. pose proof alloc_ceiling_value as (_ & HAC4).
pose proof (proj1 HE) as HLB. unfold seg_spec.SEG_C_SIZE in HLB.
destruct (ri_loc_end ly S W mem md c seg_spec.SEG_C_SIZE HAR ltac:(unfold seg_spec.SEG_C_SIZE; lia) (or_introl Hheap))
  as [Hc1 Hc2].
destruct (ri_loc_end ly S W mem md name (Z.of_nat (length nm) + 1) HAR ltac:(lia) Hloc) as [Hn1 Hn2].
unfold seg_spec.SEG_C_SIZE in Hc2.
assert (Hl : SHADOW_OFF + 2 ^ 44 + 16 <= alloc_ceiling) by (unfold SHADOW_OFF; lia).
refine (conj Hc0 (conj Hc16 (conj _ (conj Hheap (conj _ (conj Hn0 (conj _ (conj Hloc (conj _ Hlen))))))))).
- exists bs. split; [|exact HE]. apply (ri_bytes_low alloc_ceiling (rdW W mem) rd' c bs HK); [lia | lia | exact HB].
- apply (ri_addr_low alloc_ceiling (rdW W mem) rd' c _ HK); [unfold seg_spec.SEG_C_SIZE; lia | exact Hl | exact Haddr].
- apply (ri_str_low alloc_ceiling (rdW W mem) rd' name nm HK); [lia | | lia | exact Hstr].
  clear - Hn2 HAC4 Hn1. Z.div_mod_to_equations. lia.
- apply (ri_addr_low alloc_ceiling (rdW W mem) rd' name _ HK); [lia | exact Hl | exact Haddrn].
Qed.

(* arodata_okP at image A's window, of a reader that agrees with the entry's below alloc_ceiling *)
Lemma ri_arod_low : forall (W : world SEGS) mem (rd' : reader), ri_low alloc_ceiling (rdW W mem) rd' ->
  arodata_okP SEGS SegInstA.RLO_A SegInstA.RHI_A B (rdW W mem) -> arodata_okP SEGS SegInstA.RLO_A SegInstA.RHI_A B rd'.
Proof using.
intros W mem rd' HK HR a Hro Ho He. pose proof asan_consts as (C1 & _).
assert (Ha : 0 <= a < alloc_ceiling).
{ destruct Hro as [(s & Hs & _ & Hr) | Hr].
  - assert (Hi : in_img SEGS a) by (exists s; split; [exact Hs | exact Hr]).
    pose proof (pa_img_range a Hi) as Hr2. unfold kImgEnd in Hr2. lia.
  - unfold SegInstA.RLO_A, SegInstA.RHI_A, SEG_RLO, SEG_RHI in Hr. lia. }
rewrite HK by exact Ha. exact (HR a Hro Ho He).
Qed.

(* the symbolic state at the entry (check_refusal_s1.v cr_entry) *)
Lemma ri_entry : forall (W : world SEGS) (regs : bvmap 5 word) mem ly S md,
AR SEGS B ly S W mem md ->
astk_ok SegInstA.STK_reac_segconf_ignored ly (spZ regs) ->
(forall a, spZ regs - SegInstA.STK_reac_segconf_ignored <= a < spZ regs -> apresent (w_H W) mem a) ->
st_ok_pi SEGS VAL (ri_E regs) ss_ri
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_segconf_ignored)) mem (seg_rom SEGS))).
Proof using LAWS TL.
intros W regs mem ly S md HAR Hstk Hpres.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
pose proof (pal_got_cell B TL) as HGC.
pose proof (pa_obj_img 0 ltac:(lia)) as HO0. pose proof (pa_obj_img 12 ltac:(lia)) as HO12.
pose proof (pa_val_range (A_OBJ 0)) as RV0. pose proof (pa_val_range (A_OBJ 12)) as RV12.
set (E := ri_E regs).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold ri_E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs ri_extra) n)
  by (intros n Hn; subst E; unfold ri_E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 RI_SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (EO0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
  by (apply ri_ew_img; [exact HEI | unfold A_OBJ, A_TEXT, A_LIM; lia]).
assert (EO12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
  by (apply ri_ew_img; [exact HEI | unfold A_OBJ, A_TEXT, A_LIM; lia]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
unfold ss_ri. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- subst E. unfold ri_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold ri_regions, stack_region, got_regionP, bcell_regionP.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. ri_stk. lia.
  + rewrite (VB (A_OBJ 0) _ EO0 RV0). unfold kImgEnd in *. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite EO12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
  + rewrite (VB (A_OBJ 12) _ EO12 RV12). unfold kImgEnd in *. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) RI_SB);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold RI_SB; zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
- apply pairwise_disjoint_of_extents. unfold ri_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB (A_OBJ 0) _ EO0 RV0), (VB (A_OBJ 12) _ EO12 RV12).
  cbn [base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold kImgEnd in *. ri_stk.
  revert Hslo Hshi H47 Hceil C1 Hstk0 HGC HO0 HO12. clear. intros. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [ri_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, E32, !unsigned_lit_small by (unfold RI_SB; lia).
  unfold RI_SB. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  ri_stk.
  revert Hslo Hshi H47 Hceil Hal16 C1 Hstk0. clear. intros.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia | reflexivity].
Qed.

Theorem reac_segconf_ignored_walk :
  reac_segconf_ignored_contract SEGS B (BASE + AF_reac_segconf_ignored) SegInstA.STK_reac_segconf_ignored SegInstA.RLO_A SegInstA.RHI_A.
Proof using FIND LAWS TL SIGP.
unfold reac_segconf_ignored_contract.
intros ly S W regs mem md ch c name rcs nm HPRE HROD H10 Rc H11 Rn HQP HEV.
pose proof (paj_run B LAWS) as RUN.
pose proof (paj_branch (PI := PI)) as BR.
pose proof (paj_ret_at (PL := PL_seg) (PI := PI)) as RET.
pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_lt as HAC47. pose proof alloc_ceiling_value as (HACv & _).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (WS : SegInstA.STK_reac_segconf_ignored = 16 + 8224) by reflexivity.
assert (WS1 : SegInstA.STK_reac_segconf_find = 8224) by reflexivity.
rewrite WS in Hslo, Hstk0, Hbot.
(* the reader's block: a live heap block (b, m) holding the 16616 bytes of rcs at c *)
pose proof HQP as (Hc0 & Hc16 & (bs & HBS & HENC) & (b & m & Hbm & Hbc & Hcm) & _).
pose proof (proj1 HENC) as HLB. pose proof (proj1 (proj2 HENC)) as HLS. unfold seg_spec.SEG_C_SIZE in HLB, Hcm.
destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hbm) as (Hb16 & Hb4096 & Hbceil & Hbapp & _).
pose proof (req_size_pos m ltac:(lia)) as [_ Hreq].
(* the symbolic entry state *)
pose proof (ri_entry W regs mem ly S md HAR ltac:(rewrite WS; exact Hstk) ltac:(rewrite WS; exact Hpres)) as HS.
assert (SHOK : sh_ok SEGS RIx [] (ri_E regs) (mrestrict (w_H W) mem)) by constructor.
pose proof (ajournal_init SEGS B SegInstA.STK_reac_segconf_ignored [] ly S W regs mem md ch HPRE) as HJ.
assert (EL : forall n, (n < A_TEXT)%nat -> ew (ri_E regs) n = ew (Ereg regs ri_extra) n)
  by (intros n Hn; unfold ri_E; apply Eimg_low; exact Hn).
assert (HED : ed (ri_E regs) = ed (Ereg regs ri_extra)) by reflexivity.
assert (HEI : img_env VAL A_LIM (ri_E regs)) by (unfold ri_E; apply Eimg_env).
remember (ri_E regs) as E eqn:HE.
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr).
{ intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite EL by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (E1 : ew E 1 = getr regs 1) by (apply EEo; reflexivity).
assert (E2 : ew E 2 = getr regs 2) by (apply EEo; reflexivity).
assert (E3 : ew E 3 = getr regs 3) by (apply EEo; reflexivity).
assert (E4 : ew E 4 = getr regs 4) by (apply EEo; reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 c) by (rewrite (EEo 10%nat 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 name) by (rewrite (EEo 11%nat 11%bv eq_refl); exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 RI_SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs ri_extra) E).
{ split; [intros n Hn; rewrite EL by (unfold A_TEXT; lia); reflexivity | exact HED]. }
clear HE EL HED.
unfold cfg_at, w64.
(* 0x89594 .. 0x895ac: the frame, ra and s0 saved, the shadow base into s0, then jal reac_segconf_find *)
paj_run_tok RUN HS HJ SHOK RIspan.
{ awr_ok_tac. exact Usp. }
lazymatch goal with Hfr : frame_of E _ (mrestrict _ _) (mrestrict _ _) |- _ =>
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) -> rdW W (ms_mem ms) a = rdW W mem a)
by (intros a Ha Hn; apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => spZ regs - 16 <= a < spZ regs) Hfr);
  [ intros b0 wlo whi a' Hin Hrr;
      lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in replace l with l' in Hin by (vm_compute; reflexivity) end;
    repeat (destruct Hin as [Hq0 | Hin]; [injection Hq0 as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp in Hrr; lia|]);
    destruct Hin
  | exact Ha | exact Hn ]) end.
clear HF HFr HG.
assert (LOW1 : ri_low alloc_ceiling (rdW W mem) (rdW W (ms_mem ms))).
{ intros a Ha. apply KEEP1; lia. }
pose proof (proj1 HJ) as HARc.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
assert (HspT : spZ (ms_regs ms) = spZ regs + -16).
{ unfold spZ at 1. rewrite P2, Usp. rewrite unsigned_lit_small by lia. reflexivity. }
assert (P3' : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite P3, E3; exact Hgp).
assert (P4' : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite P4, E4; exact Htp).
assert (P10' : getr (ms_regs ms) 10 = w64 c) by (rewrite P10, E10; reflexivity).
assert (P11' : getr (ms_regs ms) 11 = w64 name) by (rewrite P11, E11; reflexivity).
assert (HraT : YK0s.ret_ok (getr (ms_regs ms) 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (Hra4T : 4096 <= bv_unsigned (getr (ms_regs ms) 1)) by (rewrite P1, unsigned_lit_small by lia; lia).
rewrite (SIGP SS_reac_segconf_find ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_reac_segconf_find) with AF_reac_segconf_find by (vm_compute; reflexivity).
(* 0x895ac: the call of reac_segconf_find, under its contract *)
eapply SRr_bind.
{ eapply (cl_callS B LAWS W (ms_regs ms) (ms_mem ms) _ SegInstA.STK_reac_segconf_ignored (spZ regs) [] ly S W mem md [] ly S _ 0
    SegInstA.STK_reac_segconf_find [] 0 (-16) (getr (ms_regs ms) 1) []
    (fun ly2 S2 W2 regs2 mem2 md2 => getr regs2 10 = w64 (seg_spec.find_ptr c rcs nm) /\
       sa_kept SEGS W (ms_mem ms) W2 mem2 (ms_regs ms) SegInstA.STK_reac_segconf_find (fun _ => False) /\
       sa_noalloc B ly S ly2 S2)
    HJ HspT); [reflexivity | lia | rewrite WS1; lia | rewrite WS, WS1; lia | exact P3' | exact P4' | reflexivity
    | exact HraT | exact Hra4T | | | ].
  - apply achain_low. unfold s0Z. rewrite P8, E32. rewrite unsigned_lit_small by (unfold RI_SB; lia). unfold RI_SB. lia.
  - intros HPRE1. eapply SRr_mono.
    + apply (FIND ly S W (ms_regs ms) (ms_mem ms) _ [] c name rcs nm HPRE1).
      * exact (ri_arod_low W mem _ LOW1 HROD).
      * exact P10'.
      * exact Rc.
      * exact P11'.
      * exact Rn.
      * exact (ri_qp_low ly S W mem md _ c name rcs nm HAR LOW1 HQP).
      * exact HEV.
    + cbv beta. unfold apost_base. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & HQ3).
      exists ly3, S3, regs3, mem3, md3. split; [reflexivity|]. split; [exact HJ3|]. split; [exact HP3 | exact HQ3].
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJc3 & HP3 & HQa & HKF & HNA).
pose proof (proj1 HJ3) as HAR3.
pose proof HJc3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G2 & _).
destruct (al_const _ _ LAWS _ _ _ _ _ HARc) as (Kcell2 & _ & Kgot2 & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot2. rewrite (pal_cell B TL) in Kcell2.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR3) as (Kcell3 & _ & Kgot3 & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot3. rewrite (pal_cell B TL) in Kcell3.
(* back at 0x895b0: a0 .. a7, t0 .. t6 and ra fresh atoms 40 .. 55; the frame, the GOT word and the cell kept *)
jafter_call_keep_pi HS 40%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0; 1; 2]%nat HS3.
match type of HS3 with ?t -> _ => assert (HRK : t); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | apply Forall_nil].
  - eapply (region_kept_stack_sub SEGS B); [exact HJc3 | exact HJ3 | exact Usp | lia | rewrite WS; lia | lia | lia | lia |].
    intros a _ Ha. exact (inFP_nil a Ha).
  - apply (region_kept_val_at E _ _ (A_OBJ 0) (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 12)));
    [exact (HEI (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgot2)
    | exact (val_mem_of_rdword SEGS _ _ _ _ Kgot3) | lia].
  - apply (region_kept_val_at E _ _ (A_OBJ 12) (VAL (A_OBJ 12)) 8 SHADOW_OFF);
    [exact (HEI (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kcell2)
    | exact (val_mem_of_rdword SEGS _ _ _ _ Kcell3) | lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
assert (A44 : ew (havoc E 40 (map (getr regs3) CLOB)) 44 = getr regs3 10) by reflexivity.
remember (havoc E 40 (map (getr regs3) CLOB)) as Ec eqn:HEc.
assert (HEIc : img_env VAL A_LIM Ec) by (rewrite HEc; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD3 : forall n, (n < 40)%nat -> ew Ec n = ew E n) by (intros n Hn; rewrite HEc; apply YN3v.ew_havoc_old; exact Hn).
assert (HAE3 : env_agree 32 (Ereg regs ri_extra) Ec).
{ destruct HAE as [HA1 HA2]. split; [intros n Hn; rewrite OLD3 by lia; exact (HA1 n Hn) | rewrite HEc; exact HA2]. }
clear HEc.
assert (Usp3 : bv_unsigned (ew Ec 2) = spZ regs) by (rewrite OLD3 by lia; exact Usp).
assert (SHOK3 : sh_ok SEGS RIx [] Ec (mrestrict (w_H W3) mem3)) by constructor.
rename ms into msc.
(* find's answer *)
remember (seg_spec.find_ptr c rcs nm) as fp eqn:Efp.
assert (Rfp : 0 <= fp < 2 ^ 64 /\ (fp = 0 <-> r_find rcs nm = None)).
{ rewrite Efp. unfold seg_spec.find_ptr, seg_spec.rseg_addr, seg_spec.RSEG_SIZE.
  destruct (r_find rcs nm) as [i|] eqn:RF; [|split; [lia | tauto]].
  pose proof (seg_query_facts.sq_find_lt rcs nm i RF) as Hi.
  split; [lia | split; [lia | discriminate]]. }
assert (E44 : ew Ec 44 = Z_to_bv 64 fp) by (rewrite A44, HQa; reflexivity).
(* the reader after the call: unchanged outside [sp - STK, sp) *)
assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - SegInstA.STK_reac_segconf_ignored <= a < spZ regs) ->
  rdW W3 mem3 a = rdW W mem a).
{ intros a Ha Hn. rewrite (HKF a Ha); [exact (KEEP1 a Ha ltac:(ri_stk; lia)) | rewrite HspT; ri_stk; lia | intros []]. }
rewrite P1.
(* 0x895b0: beqz a0 *)
psrr_branch_tok RUN BR HS SHOK3 RIspan.
- (* a0 = 0: no entry of that name; 0x895d0 .. 0x895dc restore and return 0 *)
  assert (Hfp0 : fp = 0).
  { rewrite branch_eq_U in Hc. apply Z.eqb_eq in Hc. rewrite (U_atom Ec 44 fp E44 (proj1 Rfp)), U_lit in Hc by lia. exact Hc. }
  clear Hc.
  assert (RF : r_find rcs nm = None) by (apply (proj2 Rfp); exact Hfp0).
  paj_run_tok RUN HS HJ3 SHOK3 RIspan.
  { awr_ok_tac. exact Usp3. }
  lazymatch goal with Hfr : frame_of Ec _ (mrestrict _ _) (mrestrict _ _) |- _ =>
  assert (KEEPF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) -> rdW W3 (ms_mem ms) a = rdW W3 mem3 a)
  by (intros a Ha Hn; apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => spZ regs - 16 <= a < spZ regs) Hfr);
    [ intros b0 wlo whi a' Hin Hrr;
      lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in replace l with l' in Hin by (vm_compute; reflexivity) end;
      repeat (destruct Hin as [Hq0 | Hin]; [injection Hq0 as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp3 in Hrr; lia|]);
      destruct Hin
    | exact Ha | exact Hn ]) end.
  prreg HS (1%bv : bv 5) F1. prreg HS (10%bv : bv 5) F10.
  eapply (RET W3 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. unfold apost_base.
  lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly3, S3, r, m, d end.
  split; [rewrite F1, OLD3, E1 by lia; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
  split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ3|].
  split; [eapply (aregs_preserved_of_st_ok SEGS _ Ec _ _ regs ri_extra HS); [exact HAE3 | vm_compute; reflexivity]|].
  split; [|split; [|exact HNA]].
  + rewrite F10, E44, Hfp0. unfold r_ignored. rewrite RF. reflexivity.
  + intros a Ha Hn _. rewrite (KEEPF a Ha) by (ri_stk; lia). exact (KEEP3 a Ha Hn).
- (* a0 = c + 356 i: the entry i of that name *)
  assert (Hfp0 : fp <> 0).
  { rewrite branch_eq_U in Hc. apply Z.eqb_neq in Hc. rewrite (U_atom Ec 44 fp E44 (proj1 Rfp)), U_lit in Hc by lia. exact Hc. }
  clear Hc.
  destruct (r_find rcs nm) as [i|] eqn:RF; [|exfalso; apply Hfp0; apply (proj2 Rfp); reflexivity].
  pose proof (seg_query_facts.sq_find_lt rcs nm i RF) as Hi.
  assert (Hp : fp = c + 356 * Z.of_nat i)
    by (rewrite Efp; unfold seg_spec.find_ptr, seg_spec.rseg_addr, seg_spec.RSEG_SIZE; rewrite RF; reflexivity).
  assert (Hp4 : (c + 356 * Z.of_nat i) mod 4 = 0) by (clear - Hc16; Z.div_mod_to_equations; lia).
  (* the block is live after the call: its shadow and its bytes *)
  assert (Hbm3 : In (b, m) (ablocks B ly3 S3))
    by (eapply Permutation_in; [apply Permutation_sym; exact (proj1 HNA) | exact Hbm]).
  assert (ZR : range_addressable (rdW W3 mem3) SHADOW_OFF (fp + 24) 4)
    by (apply (range_addressable_of_block SEGS B LAWS ly3 S3 W3 mem3 md3 b m); [exact HAR3 | exact Hbm3 | lia | lia]).
  pose proof (ri_ignore_val (rdW W mem) c bs rcs i HBS HENC Hi) as VF0.
  assert (VF2 : sa_val (rdW W3 mem3) (fp + 24) 4 (seg_spec.b2z (rs_ignore (r_seg rcs i)))).
  { intros k Hk. rewrite Hp. rewrite <- (VF0 k Hk). rewrite <- (LOW1 (c + 356 * Z.of_nat i + 24 + Z.of_nat k)) by lia.
    replace (c + 356 * Z.of_nat i + 24 + Z.of_nat k) with (b + (c + 356 * Z.of_nat i + 24 + Z.of_nat k - b)) by lia.
    apply (G2 b m); [exact Hbm | exact Hbm3 | lia | intros Hf; exact (inFP_nil _ Hf)]. }
  assert (SHOK4 : sh_ok SEGS RIx ri_SH Ec (mrestrict (w_H W3) mem3)).
  { unfold sh_ok, ri_SH. constructor; [|constructor].
    apply (shent_ok_of_range SEGS (w_H W3) mem3 Ec RIx 44 (fp + 24) 4 fp 24 28 ZR).
    - unfold U, RIx. cbn [sv_denot]. rewrite OLD3 by lia. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by (unfold RI_SB; lia). reflexivity.
    - exact (U_atom Ec 44 fp E44 (proj1 Rfp)).
    - lia.
    - lia.
    - intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia. }
  pose proof (pa_obj_img 0 ltac:(lia)) as HO0. pose proof (pa_obj_img 12 ltac:(lia)) as HO12.
  pose proof (blk_off_imgP B _ _ _ _ _ b m HAR3 Hbm3) as HOFF. unfold off_img in HOFF.
  (* the pointer's fact and the ignore field's region, then 0x895b4 .. 0x895dc: the check passes, the load gives the
     flag, snez keeps it, restore and return *)
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ =>
    let v := eval vm_compute in ssx in replace ssx with v in HS by (vm_compute; reflexivity) end.
  apply (st_ok_pi_add_fact Ec _ _ 44%nat ri_pfact) in HS;
    [| unfold afact_ok, ri_pfact; cbn [af_lo af_hi af_al2]; rewrite E44, unsigned_lit_small by lia; rewrite Hp;
       change (2 ^ 2) with 4; lia].
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ =>
    let v := eval vm_compute in ssx in replace ssx with v in HS by (vm_compute; reflexivity) end.
  destruct (rs_ignore (r_seg rcs i)) eqn:IG; cbn [seg_spec.b2z] in VF2.
  all: lazymatch type of VF2 with sa_val _ _ _ ?v => apply (st_ok_pi_add_region Ec _ _ (ri_field v)) in HS end.
  all: lazymatch goal with
    | |- region_wf _ = true => vm_compute; reflexivity
    | |- region_ok _ _ _ _ =>
        cbn [ms_mem restrict mkst]; unfold region_ok, ri_field;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
        rewrite E44, unsigned_lit_small by lia;
        split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
        apply Forall_cons; [|apply Forall_nil];
        lazymatch type of VF2 with sa_val _ _ _ ?v =>
          apply (chunk_ok_val SEGS Ec _ fp 24 4 (SLit v) v);
          [reflexivity | zside | zside | exact (ri_val_of_sa SEGS _ _ _ _ _ VF2)] end
    | |- all_disjoint _ _ _ =>
        apply all_disjoint_of_extents; unfold extent_of_region, ri_field;
        cbn [map YP09.r_base YP09.r_lo YP09.r_hi zall_disjoint ss_mem base_val]; unfold zdisj; cbn [fst snd];
        rewrite E44, unsigned_lit_small by lia;
        rewrite ?Usp3, ?(HEIc 241%nat ltac:(unfold A_TEXT, A_LIM; lia)), ?(HEIc 253%nat ltac:(unfold A_TEXT, A_LIM; lia));
        change (VAL 241%nat) with (VAL (A_OBJ 0)); change (VAL 253%nat) with (VAL (A_OBJ 12));
        unfold kImgEnd in *; ri_stk; repeat split; lia
    | |- _ => idtac
  end.
  all: paj_run_tok RUN HS HJ3 SHOK4 RIspan.
  all: lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ _ _ _ => awr_ok_tac; exact Usp3 | |- _ => idtac end.
  all: lazymatch goal with Hfr : frame_of ?E0 _ (mrestrict _ _) (mrestrict _ _) |- _ =>
  assert (KEEPF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) -> rdW W3 (ms_mem ms) a = rdW W3 mem3 a)
  by (intros a Ha Hn; apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => spZ regs - 16 <= a < spZ regs) Hfr);
    [ intros b0 wlo whi a' Hin Hrr;
      lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in replace l with l' in Hin by (vm_compute; reflexivity) end;
      repeat (destruct Hin as [Hq0 | Hin]; [injection Hq0 as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp3 in Hrr; lia|]);
      destruct Hin
    | exact Ha | exact Hn ]) end.
  all: prreg HS (1%bv : bv 5) F1; prreg HS (10%bv : bv 5) F10.
  all: eapply (RET W3 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  all: intros mat'; unfold apost_base.
  all: lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly3, S3, r, m, d end.
  all: split; [rewrite F1, OLD3, E1 by lia; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
  all: split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ3|].
  all: lazymatch type of HS with st_ok_pi _ _ ?E4 _ _ =>
    assert (HAE4 : env_agree 32 (Ereg regs ri_extra) E4) by
      (destruct HAE3 as [HA1 HA2]; split;
       [ intros n Hn; cbn [ew ewset];
         repeat match goal with |- context [Nat.eqb ?a ?b] => destruct (Nat.eqb_spec a b); [lia|] end; exact (HA1 n Hn)
       | cbn [ed ewset]; exact HA2 ]) end.
  all: split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs ri_extra HS); [exact HAE4 | vm_compute; reflexivity]|].
  all: split; [|split; [|exact HNA]].
  all: lazymatch goal with
    | |- getr _ _ = _ => rewrite F10; unfold r_ignored; rewrite RF, IG; reflexivity
    | |- sa_kept _ _ _ _ _ _ _ _ => intros a Ha Hn _; rewrite (KEEPF a Ha) by (ri_stk; lia); exact (KEEP3 a Ha Hn)
  end.
Qed.
End e.
End f.
End d.
