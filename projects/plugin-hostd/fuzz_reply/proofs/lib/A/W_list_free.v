(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of fuzz_reply's list_free, in the form of the cgif walks of
   proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v (free sites) and lib/A/AC8b.v (loops). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d YI00 YN0h.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_syms W_listing W_pl W_kit W_journal W_rep W_contract W_sites W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG FCiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YCe5x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_journal_x W_kit_x W_sites_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_contract_srlf_xR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep ListRep.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).
Definition A_list_free : Z := AF_fr_list_free.
Definition A_list_freeP : Z := BASE + A_list_free.
Definition A_lf_lw : Z := AF_fr_list_free + 0x50.     (* 0x860d0: lw s7,0(s1), the first access of the list *)
Definition A_lf_loop : Z := AF_fr_list_free + 0x68.   (* 0x860e8: the loop head *)
Definition A_lf_done : Z := AF_fr_list_free + 0xe4.   (* 0x86164: after the loop *)
Definition LF_FRAME : Z := 80.

(* ---- bytes of the vector: struct text { char *s; size_t n; }, 16 bytes each ---- *)
Lemma lf_nth_le_bytes : forall n z k, (k < n)%nat ->
nth k (Z_to_le_bytes n z) (Z_to_bv 8 0) = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
induction n as [|n IH]; intros z k Hk; [lia|]. destruct k as [|k]; cbn [Z_to_le_bytes nth].
- replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r. reflexivity.
- rewrite IH by lia. f_equal. rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.
Lemma lf_le8_val : forall m a (w : word), garr8 SEGS m a (bzs (Mem.le8 w)) -> val_mem SEGS m a 8 (bv_unsigned w).
Proof.
intros m a w H k Hk.
assert (Hlen : (k < length (bzs (Mem.le8 w)))%nat) by (unfold bzs; rewrite length_map, Mem.length_le8; exact Hk).
rewrite (garr8_mbyte SEGS m a _ k H Hlen). f_equal.
unfold bzs. rewrite (nth_indep _ 0 (bz (Z_to_bv 8 0))) by exact Hlen. rewrite map_nth.
unfold Mem.le8, word_to_le_bytes, bz. rewrite lf_nth_le_bytes by lia. rewrite Z_to_bv_bv_unsigned.
pose proof (bv_unsigned_in_range 64 w) as Hw. change (bv_modulus 64) with (2 ^ 64) in Hw.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
unfold YO0f.le_byte. replace (8 * Z.of_nat 8) with 64 by lia. rewrite (Z.mod_small (bv_unsigned w)) by lia.
rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma lf_len_text_recs : forall l, length (concat (map text_rec l)) = (16 * length l)%nat.
Proof.
induction l as [|r l IH]; [reflexivity|]. cbn [map concat]. rewrite length_app, IH. unfold text_rec.
rewrite length_app, !Mem.length_le8. cbn [length]. lia.
Qed.
(* the pointer of record i, read at v + 16 i *)
Lemma lf_slot_val : forall m v (recs : list (Z * list byte)) junk i,
garr8 SEGS m v (bzs (concat (map text_rec recs) ++ junk)) -> (i < length recs)%nat ->
val_mem SEGS m (v + 16 * Z.of_nat i) 8 (bv_unsigned (Z_to_bv 64 (fst (nth i recs (0, []))))).
Proof.
intros m v recs junk i H Hi.
assert (Hr : nth i recs (0, []) = nth 0 (skipn i recs) (0, [])) by (rewrite nth_skipn, Nat.add_0_r; reflexivity).
rewrite <- (firstn_skipn i recs) in H. rewrite map_app, concat_app in H.
destruct (skipn i recs) as [|r rest] eqn:Es; [apply (f_equal (@length _)) in Es; rewrite length_skipn in Es; cbn in Es; lia|].
cbn [nth] in Hr. rewrite Hr. clear Hr.
cbn [map concat] in H. unfold text_rec at 1 in H. unfold bzs in H.
rewrite <- !app_assoc, map_app in H. apply garr8_app in H as [_ H].
rewrite map_app in H. apply garr8_app in H as [H _].
rewrite length_map, lf_len_text_recs, length_firstn in H. replace (Nat.min i (length recs)) with i in H by lia.
replace (v + Z.of_nat (16 * i)) with (v + 16 * Z.of_nat i) in H by lia.
unfold text_rec in H. rewrite map_app in H. apply garr8_app in H as [H _].
exact (lf_le8_val m _ _ H).
Qed.
(* dropping the last of the blocks being freed *)
Lemma lf_perm_drop : forall (l1 l2 A B R : list (Z * Z)) x,
Permutation (l1 ++ x :: l2) (A ++ (B ++ [x]) ++ R) -> Permutation (l1 ++ l2) (A ++ B ++ R).
Proof.
intros l1 l2 A B R x H. apply (Permutation_app_inv l1 l2 [] (A ++ B ++ R) x).
rewrite app_nil_l. eapply Permutation_trans; [exact H|]. rewrite <- !app_assoc. cbn [app].
rewrite (app_assoc A B (x :: R)), (app_assoc A B R). apply Permutation_sym. apply Permutation_middle.
Qed.
Lemma lf_perm_drop2 : forall (l1 l2 A Bm R : list (Z * Z)) x,
Permutation (l1 ++ x :: l2) ((A ++ (Bm ++ [x])) ++ R) -> Permutation (l1 ++ l2) ((A ++ Bm) ++ R).
Proof.
intros l1 l2 A Bm R x H. rewrite <- (app_assoc A Bm R). apply (lf_perm_drop l1 l2 A Bm R x).
rewrite <- (app_assoc A (Bm ++ [x]) R) in H. exact H.
Qed.
Lemma lf_in_drop : forall (x y : Z * Z) b1 b2 l1, l1 = b1 ++ y :: b2 -> In x l1 -> x <> y -> In x (b1 ++ b2).
Proof.
intros x y b1 b2 l1 -> Hin Hne. apply in_app_or in Hin as [H | [H | H]];
[apply in_or_app; left; exact H | exfalso; apply Hne; symmetry; exact H | apply in_or_app; right; exact H].
Qed.
(* the room round (W_contract_x.v lf_spec_x at 475b8a2b569): a free keeps the live counts under their bounds (one
   block fewer, W_journal_x.v acnt_del_le); list_free's room budget is one free per text and one for the vector *)
Lemma lf_cnt_del : forall RP0 l1 (x : Z * Z) l2, cnt_ok RP0 (l1 ++ x :: l2) -> cnt_ok RP0 (l1 ++ l2).
Proof.
intros RP0 l1 x l2 H. unfold cnt_ok in *.
apply (cnt_ok_pk_mono RP0 (fun _ => 0%nat) (fun _ => 0%nat) (l1 ++ x :: l2) (l1 ++ l2)); [|exact H].
intros P. cbv beta. rewrite !Nat.add_0_r. apply acnt_del_le.
Qed.
Lemma lf_rm_cast : forall RP0 S0 (m m' : nat), rp_RM RP0 S0 m -> m = m' -> rp_RM RP0 S0 m'.
Proof. intros RP0 S0 m m' H <-. exact H. Qed.
Lemma lf_rk : forall l, Z.to_nat (lf_cost MT_rk l) = Datatypes.S (length (hl_recs l)).
Proof. intros l. unfold lf_cost, hl_n. cbn [mo_free MT_rk]. lia. Qed.
(* a region kept across a call that may change the world *)
Lemma lf_region_kept2 : forall E (W W2 : world SEGS) (m m2 : word -> option byte) n b lo hi wlo whi cs,
bv_unsigned (ew E n) = b ->
(forall a, b + lo <= a < b + hi -> aview SEGS (w_H W2) m2 a = aview SEGS (w_H W) m a) ->
(forall a, b + wlo <= a < b + whi -> writable_at SEGS (mrestrict (w_H W) m) a -> writable_at SEGS (mrestrict (w_H W2) m2) a) ->
region_kept SEGS E (mrestrict (w_H W) m) (mrestrict (w_H W2) m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E W W2 m m2 n b lo hi wlo whi cs Hn Hv Hw.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hv. exact Ha.
- apply Hw. exact Ha.
Qed.
(* an image byte stays writable when its presence is kept (W_lp_tail.v lpt_writable_img) *)
Lemma lf_writable_img : forall (Wa Wb : world SEGS) (m m' : word -> option byte) a,
in_img SEGS a -> (apresent (w_H Wa) m a -> apresent (w_H Wb) m' a) ->
writable_at SEGS (mrestrict (w_H Wa) m) a -> writable_at SEGS (mrestrict (w_H Wb) m') a.
Proof.
intros Wa Wb m m' a Hi Hp Hw.
assert (Ha : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit_small; pose proof (pa_segs_low a Hi); unfold kLowMemEnd in *; lia).
assert (HA : w_H Wa (Z_to_bv 64 a) = false) by (apply hidden_not_img; rewrite Ha; exact Hi).
assert (HB : w_H Wb (Z_to_bv 64 a) = false) by (apply hidden_not_img; rewrite Ha; exact Hi).
unfold writable_at, wview, mrestrict in *. rewrite HA in Hw. rewrite HB.
destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em.
- destruct (Hp (conj HA (ex_intro _ b Em))) as [_ [b2 Hb2]]. rewrite Hb2. discriminate.
- destruct (m' (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.
Lemma lf_apresent_grows : forall H (m m' : word -> option byte) a,
mem_grows (mrestrict H m) (mrestrict H m') -> apresent H m a -> apresent H m' a.
Proof.
intros H m m' a Hg [Hh [b Hb]]. split; [exact Hh|].
assert (Hx : mrestrict H m (Z_to_bv 64 a) <> None) by (unfold mrestrict; rewrite Hh, Hb; discriminate).
specialize (Hg _ Hx). unfold mrestrict in Hg. rewrite Hh in Hg.
destruct (m' (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity | exfalso; apply Hg; reflexivity].
Qed.
Lemma lf_garr8_kept : forall H H' (m m' : word -> option byte) a l,
(forall j, 0 <= j < Z.of_nat (length l) -> aview SEGS H' m' (a + j) = aview SEGS H m (a + j)) ->
garr8 SEGS (mrestrict H m) a l -> garr8 SEGS (mrestrict H' m') a l.
Proof.
intros H H' m m' a l HK Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (val_mem_kept SEGS H H' m m' (a + Z.of_nat j) 1); [|exact Hv].
intros k Hk. rewrite <- !Z.add_assoc. apply HK. lia.
Qed.
(* W_kit's prreg without the normalisation: the register's symbolic value stays as the engine wrote it *)
Ltac prreg_raw HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
cbn [ms_regs restrict mkst] in Hr
end.
(* the side conditions of a view-keeping fact at errno's byte as_errno B + i (ERF: lf_errno_facts below) *)
Ltac lf_err_side ERF i Hi :=
first [ exact (proj1 (ERF i Hi)) | exact (proj1 (proj2 (ERF i Hi)))
      | let Hx := fresh in intros Hx; apply (proj2 (proj2 (ERF i Hi))); revert Hx; clear; unfold ESTACK, LF_STK, ASTACK; lia ].
(* ---- THE WALK OVER THE GENERIC RELATION (route (b), step 3; CONVERSION.md (sha256 1015972e02a9; internal record)): list_free
   over any ARx with its laws, stated as W_contract_x.lf_spec_x.  The Section hypotheses beyond the AR walk's: PST /
   ARx / hl / LAWS (the generic relation), HP0 (the unit's hidden-head set is empty in every ARx state: fuzz_reply
   calls no poison routine; a Theorem Labs lane's ruling, so YCbqG.ARx_shadow_law's premise holds at every state:
   W_journal_x's range_addressable_of_block_hp0_x), IMGC / BLKN (W_kit_x.v Section g, for blk_off_imgP_x), PSTR
   (the ROM bytes are off the program statics PST: W_journal_x.ajournal_gx_rom_view_x's premise, for the memmove's
   rom_view), and the allocator's free rules in their caller-context form (W_journal_x Section hc, `Variable CTX`):
   both free calls hand the rule the chain [] (s0 holds the list head LA, an image address), so each call's trace is
   the singleton [its return address], a closed fact HCTX_lf_loop / HCTX_lf_exit (fuzz_reply.objdump: the loop's
   free returns to list_free + 0x98, the exit's free / free(NULL) to list_free + 0xf8).  RP is the room record of
   the texts (W_journal_x.v roomp, the rules' and the spec's): the loop invariant carries the room left
   (c + 1 + kr, one free per text left and one for the vector) and the live counts at the loop head, which only
   fall (each free drops one block, lf_cnt_del); each free hands the rule its stack room (aj_stack_room_x). ---- *)
Section c.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable G : list (Z * Z).
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis IMGC : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
fst (ly_img ly) <= 0x10000 /\ 0x5fb000 <= fst (ly_img ly) + snd (ly_img ly).
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Hypothesis PSTR : forall a, in_rom SEGS a -> ~ Exists (in_zr a) PST.
Hypothesis HG : gx_ok SEGS B G.
Hypothesis MLAW : ameter_laws MT.
Variable CTX : list (list Z).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX.
Hypothesis AFREEN : afree_null_cf_rule_c_x SEGS B PST ARx MT RP CTX.
Hypothesis HCTX_lf_loop : In [BASE + AF_fr_list_free + 0x98] CTX.
Hypothesis HCTX_lf_exit : In [BASE + AF_fr_list_free + 0xf8] CTX.
Hypothesis TL : PALib B.
Hypothesis AMOVE : amemmove_realizes_x B ARx (SIGMA WS_asan_memmove).
Hypothesis HGR : gx_rt B G.
Hypothesis HRO : rom_out SEGS B G.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let HBfree := pal_free B TL.
Let RUN := paj_run_x_x B PST ARx LAWS G HG 0 [].
Let RUNTO := paj_run_to_x_x B PST ARx LAWS G HG 0 [].
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).

(* errno's four bytes lie in the image (PALib's api_env): off the list struct (gx_rt) and below every stack frame *)
Lemma lf_errno_facts : forall (sp LA : Z), alloc_ceiling <= sp - LF_STK -> (forall a, LA <= a < LA + 16 -> inG G a) ->
forall i, 0 <= i < 4 ->
0 <= as_errno B + i < 2 ^ 64 /\ ~ (LA <= as_errno B + i < LA + 16) /\ ~ (sp - LF_STK <= as_errno B + i < sp).
Proof.
intros sp LA Hsp HLG i Hi. pose proof (pal_env B TL) as ((HE0 & HE1) & _ & _).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). rewrite C5 in HE1.
split; [lia|]. split.
- intros Hin. exact (proj1 (HGR _ (HLG _ Hin)) ltac:(lia)).
- unfold LF_STK, ASTACK in *. lia.
Qed.
(* ---- the list struct: v at +0, n at +8, cap at +12, all writable ---- *)
Definition lf_lreg (m : nat) (cv cn cc : sv) : YP09.region :=
YP09.mkRegion (Some m) 0 16 0 16
[YP09.mkChunk 0 (CVal 8 cv); YP09.mkChunk 8 (CVal 4 cn); YP09.mkChunk 12 (CVal 4 cc)].
Lemma lf_lreg_ok : forall E W mem m LA cv cn cc v n cap,
bv_unsigned (ew E m) = LA -> 0 <= LA -> LA + 16 <= 2 ^ 64 ->
sv_denot E cv = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E cn = Z_to_bv 64 n -> 0 <= n < 2 ^ 32 ->
sv_denot E cc = Z_to_bv 64 cap -> 0 <= cap < 2 ^ 32 ->
val_mem SEGS (arm W mem) LA 8 v -> val_mem SEGS (arm W mem) (LA + 8) 4 n -> val_mem SEGS (arm W mem) (LA + 12) 4 cap ->
awr W mem LA 16 -> region_ok SEGS E (arm W mem) (lf_lreg m cv cn cc).
Proof.
intros E W mem m LA cv cn cc v n cap Hm H0 H1 Hv Rv Hn Rn Hc Rc Mv Mn Mc Hw. unfold region_ok, lf_lreg.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Hm.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hw; lia|].
constructor; [|constructor; [|constructor; [|constructor]]].
- apply (chunk_ok_val SEGS E _ LA 0 8 cv v); [exact Hv | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Mv].
- apply (chunk_ok_val SEGS E _ LA 8 4 cn n); [exact Hn | cbn; lia | cbn; lia | exact Mn].
- apply (chunk_ok_val SEGS E _ LA 12 4 cc cap); [exact Hc | cbn; lia | cbn; lia | exact Mc].
Qed.
Lemma lf_disj : forall LA g, (forall a, LA <= a < LA + 16 -> ~ (g <= a < g + 8)) -> LA + 16 <= g \/ g + 8 <= LA.
Proof.
intros LA g H. destruct (Z_le_gt_dec (LA + 16) g) as [H1|H1]; [left; exact H1|].
destruct (Z_le_gt_dec (g + 8) LA) as [H2|H2]; [right; exact H2|]. exfalso. apply (H (Z.max LA g)); lia.
Qed.
Lemma lf_LA_range : forall LA, (forall a, LA <= a < LA + 16 -> inG G a) ->
0x10000 <= LA /\ LA + 16 <= 0x5fb000 /\
(LA + 16 <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= LA) /\ (LA + 16 <= VAL (A_OBJ 32) \/ VAL (A_OBJ 32) + 8 <= LA) /\
(forall a, LA <= a < LA + 16 -> ~ (as_errno B <= a < as_errno B + 4)).
Proof.
intros LA HLG.
pose proof (pa_img_range LA (proj1 (HG LA (HLG LA ltac:(lia))))) as H1.
pose proof (pa_img_range (LA + 15) (proj1 (HG (LA + 15) (HLG (LA + 15) ltac:(lia))))) as H2.
split; [lia|]. split; [lia|].
split; [apply lf_disj; intros a Ha; exact (proj1 (proj2 (HGR a (HLG a Ha))))|].
split; [apply lf_disj; intros a Ha; exact (proj2 (proj2 (HGR a (HLG a Ha))))|].
intros a Ha. exact (proj1 (HGR a (HLG a Ha))).
Qed.

(* ---- the entry ---- *)
Definition lf_Bx : sv := SOff 35 0.
Definition lf_regions0 : smem :=
[ stack_region LF_FRAME; got_regionP; bcell_regionP 35; lf_lreg 10 (SOff 32 0) (SOff 33 0) (SOff 34 0) ].
Definition lf_facts0 : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF 0x10000 (0x5fb000 - 16) 0);
(33%nat, mkAF 0 (2 ^ 30 - 1) 0); (34%nat, mkAF 0 (2 ^ 30 - 1) 0); (35%nat, mkAF SB SB 0) ] [] [].
Definition ss_lf0 : sstate := mkSS A_list_free sr_atoms lf_regions0 None lf_facts0.
Definition lf_SH : list shent := [ mkSHE 10 0 16 ].
Definition lf_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition lf_extra (l : hlist) : list word := map (Z_to_bv 64) [hl_v l; hl_n l; hl_cap l; SB].

Lemma lf_entry_x : forall W ly S Hp regs mem md ch LA (l : hlist) lines,
afn_pre_x SEGS B ARx LF_STK ly S Hp W regs mem md ch ->
getr regs 10 = w64 LA ->
alist_at B ly S W mem LA l lines ->
(forall a, LA <= a < LA + 16 -> inG G a) -> azs B LA 16 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (lf_extra l))) ss_lf0
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_list_freeP) mem (seg_rom SEGS)))
/\ sh_ok SEGS lf_Bx lf_SH (Eimg (Ereg regs (lf_extra l))) (mrestrict (w_H W) mem).
Proof.
intros W ly S Hp regs mem md ch LA l lines HPRE H10 HL HLG HZS.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof (lf_LA_range LA HLG) as (HLA1 & HLA2 & DG & DC & _).
pose proof HL as (Mv & Mn & Mc & Hw & (Hn0 & Hcap) & _).
assert (WS : LF_STK = 16464) by reflexivity.
destruct (alx_const _ _ _ LAWS ly S Hp W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (lf_extra l))). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 LA) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 (hl_v l)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (hl_n l)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (hl_cap l)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E273 : ew E (A_OBJ 32) = Z_to_bv 64 (VAL (A_OBJ 32))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 32 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall m w, ew E m = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some m) = w).
{ intros m w Hm Hw'. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hw'. }
assert (HnZ : 0 <= hl_n l) by (unfold hl_n; lia).
assert (Hv64 : 0 <= hl_v l < 2 ^ 64).
{ destruct HL as (_ & _ & _ & _ & _ & [[_ ->] | (Hcp & Hin & _)] & _); [lia|].
  destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hin) as (_ & H4096 & Hce & _).
  unfold req_size, AREC in Hce. destruct (Z.eqb_spec (16 * hl_cap l) 0); unfold alloc_ceiling in *; lia. }
split.
- unfold ss_lf0, A_list_freeP. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold lf_regions0, stack_region, got_regionP, bcell_regionP, LF_FRAME.
repeat apply Forall_cons; try apply Forall_nil.
* unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
* unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 32) 0) (VAL (A_OBJ 32)));
[cbn [sv_denot]; rewrite E273, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 32)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
* unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
rewrite (VB (A_OBJ 32) (VAL (A_OBJ 32)) E273) by (pose proof (pa_val_range (A_OBJ 32)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 32)) 0 8 lf_Bx SB);
[cbn [sv_denot lf_Bx]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
* apply (lf_lreg_ok E W mem 10 LA _ _ _ (hl_v l) (hl_n l) (hl_cap l)).
-- rewrite E10. apply unsigned_lit_small. lia.
-- lia.
-- lia.
-- cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
-- exact Hv64.
-- cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
-- lia.
-- cbn [sv_denot]. rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
-- lia.
-- exact Mv.
-- exact Mn.
-- exact Mc.
-- exact Hw.
+ apply pairwise_disjoint_of_extents. unfold lf_regions0, lf_lreg, stack_region, got_regionP, bcell_regionP, extent_of_region, LF_FRAME.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
rewrite (VB (A_OBJ 32) (VAL (A_OBJ 32)) E273) by (pose proof (pa_val_range (A_OBJ 32)); lia).
rewrite (VB 10%nat LA E10) by lia. cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 HcellR HgcD HgotR HLA1 HLA2 DG DC. clear.
unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [lf_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E33, E34, E35, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil Hal16 C1 C3 WS Hstk0 HLA1 HLA2 Hn0 Hcap HnZ. clear.
unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros.
repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, lf_SH. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) mem E lf_Bx 10 LA 16 LA 0 16).
+ exact (azs_range_addressable_x B ARx LAWS ly S Hp W mem md LA 16 HAR HZS).
+ unfold U, lf_Bx. cbn [sv_denot]. rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
+ lia.
+ lia.
+ intros x Hx. unfold SHADOW_OFF. cbn in Hx. lia.
Qed.

(* ---- the loop head (0x860e8) and the exit (0x86164), entered afresh from concrete facts ----
   Atoms: 0..31 the current registers; 32 v, 33 cap, 34..43 the entry's s8 s7 s6 s5 s4 s3 s2 s1 s0 ra (the frame's
   ten slots from sp up), 44 the text pointer the iteration frees, 45 its slot v + 16 (n - 1). *)
Definition lf_saved : list Z := [24; 23; 22; 21; 20; 19; 18; 9; 8; 1].
Definition lf_frame (W : world SEGS) (mem : word -> option byte) (sp0 : Z) (regs0 : bvmap 5 word) : Prop :=
forall i, (i < 10)%nat ->
val_mem SEGS (arm W mem) (sp0 - 80 + 8 * Z.of_nat i) 8 (bv_unsigned (getr regs0 (Z_to_bv 5 (nth i lf_saved 0)))).
Definition lf_regs (regs regs0 : bvmap 5 word) (LA c : Z) : Prop :=
getr regs 2 = Z_to_bv 64 (spZ regs0 - 80) /\ getr regs 3 = getr regs0 3 /\ getr regs 4 = getr regs0 4 /\
getr regs 8 = Z_to_bv 64 LA /\ getr regs 9 = Z_to_bv 64 (LA + 8) /\ getr regs 18 = Z_to_bv 64 SB /\
getr regs 19 = Z_to_bv 64 ((LA + 8) / 8 + SB) /\ getr regs 20 = Z_to_bv 64 (LA / 8) /\
getr regs 21 = Z_to_bv 64 (LA / 8 + SB) /\ getr regs 23 = Z_to_bv 64 c /\
getr regs 25 = getr regs0 25 /\ getr regs 26 = getr regs0 26 /\ getr regs 27 = getr regs0 27.
Definition lf_sp0 (sp0 : Z) : Prop := sp0 mod 16 = 0 /\ alloc_ceiling + 80 <= sp0 <= 2 ^ 47.
Definition lf_xl (v cap s d : Z) (regs0 : bvmap 5 word) : list word :=
map (Z_to_bv 64) [v; cap] ++ map (fun r => getr regs0 (Z_to_bv 5 r)) lf_saved ++ map (Z_to_bv 64) [s; d].
Definition lf_stackL : YP09.region :=
YP09.mkRegion (Some 2%nat) 0 80 0 0 (map (fun i => YP09.mkChunk (8 * Z.of_nat i) (CVal 8 (SOff (34 + i) 0))) (seq 0 10)).
Definition lf_BxL : sv := SOff 18 0.
Definition lf_srL : list sv :=
sr_set (sr_set (sr_set (sr_set sr_atoms 9%bv (SOff 8 8))
19%bv (SAlu ALU_ADD (SAlu ALU_SRL (SOff 8 8) (SLit 3)) (SOff 18 0)))
20%bv (SAlu ALU_SRL (SOff 8 0) (SLit 3)))
21%bv (SAlu ALU_ADD (SAlu ALU_SRL (SOff 8 0) (SLit 3)) (SOff 18 0)).
Definition lf_lregL : YP09.region := lf_lreg 8 (SOff 32 0) (SOff 23 0) (SOff 33 0).
Definition lf_slotL : YP09.region := YP09.mkRegion (Some 45%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 44 0))].
(* v + 16 * (c - 1): the engine's canonical form of the slot address; an alias to atom 45 lets aliased2
   rewrite it (and so every shadow/data address built on it) to a single atom. *)
Definition lf_aexpr : sv :=
SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SLL (SOff 23 0) (SLit 4)) (SLit (-16))) (SOff 32 0).
Definition lf_atomsL (n23 : afact) : list (nat * afact) :=
[ (2%nat, mkAF (2^46) (2^47) 4); (8%nat, mkAF 0x10000 (0x5fb000 - 16) 0); (18%nat, mkAF SB SB 0); (23%nat, n23) ].
Definition ss_lfL : sstate :=
mkSS A_lf_loop lf_srL [lf_stackL; lf_lregL; lf_slotL] None
(mkFacts (lf_atomsL (mkAF 1 (2 ^ 30 - 1) 0) ++ [(45%nat, mkAF 4096 0x7fffff800000 4)]) [] [(lf_aexpr, SOff 45 0)]).
Definition lf_SHL : list shent := [mkSHE 8 0 16; mkSHE 45 0 8].
(* after the loop (0x86164), entered afresh: s4 = LA >> 3 is all the exit reads of the loop's registers, l->n is 0 *)
Definition lf_srX : list sv := sr_set sr_atoms 20%bv (SAlu ALU_SRL (SOff 8 0) (SLit 3)).
Definition lf_lregX : YP09.region := lf_lreg 8 (SOff 32 0) (SLit 0) (SOff 33 0).
Definition lf_factsX : facts :=
mkFacts [(2%nat, mkAF (2^46) (2^47) 4); (8%nat, mkAF 0x10000 (0x5fb000 - 16) 0); (18%nat, mkAF SB SB 0)] [] [].
Definition ss_lfX0 : sstate := mkSS A_lf_done sr_atoms [lf_stackL; lf_lregX] None lf_factsX.
Definition ss_lfX : sstate := mkSS A_lf_done lf_srX [lf_stackL; lf_lregX] None lf_factsX.
Definition lf_regsT (regs regs0 : bvmap 5 word) (LA : Z) : Prop :=
getr regs 2 = Z_to_bv 64 (spZ regs0 - 80) /\ getr regs 3 = getr regs0 3 /\ getr regs 4 = getr regs0 4 /\
getr regs 8 = Z_to_bv 64 LA /\ getr regs 18 = Z_to_bv 64 SB /\ getr regs 20 = Z_to_bv 64 (LA / 8) /\
getr regs 25 = getr regs0 25 /\ getr regs 26 = getr regs0 26 /\ getr regs 27 = getr regs0 27.
Definition lf_SHT : list shent := [mkSHE 8 0 16].

Lemma lf_ew_saved : forall regs regs0 v cap s d i, (i < 10)%nat ->
ew (Eimg (Ereg regs (lf_xl v cap s d regs0))) (34 + i) = getr regs0 (Z_to_bv 5 (nth i lf_saved 0)).
Proof.
intros regs regs0 v cap s d i Hi. rewrite Eimg_low by (unfold A_TEXT; lia).
replace (34 + i)%nat with (32 + (2 + i))%nat by lia. rewrite ew_Ereg_extra.
do 10 (destruct i as [|i]; [reflexivity|]). lia.
Qed.
(* the entry's own saved registers (the prologue stores them from the registers themselves) *)
Lemma lf_ew_regs : forall regs extra i, (i < 10)%nat ->
ew (Eimg (Ereg regs extra)) (Z.to_nat (nth i lf_saved 0)) = getr regs (Z_to_bv 5 (nth i lf_saved 0)).
Proof.
intros regs extra i Hi.
do 10 (destruct i as [|i]; [rewrite Eimg_low by (unfold A_TEXT; cbn; lia); apply ew_Ereg_nat; vm_compute; reflexivity|]). lia.
Qed.
Lemma lf_stackL_ok : forall E W mem sp0 regs0,
bv_unsigned (ew E 2) = sp0 - 80 -> 0 <= sp0 - 80 -> sp0 <= 2 ^ 64 ->
(forall i, (i < 10)%nat -> ew E (34 + i) = getr regs0 (Z_to_bv 5 (nth i lf_saved 0))) ->
lf_frame W mem sp0 regs0 -> region_ok SEGS E (arm W mem) lf_stackL.
Proof.
intros E W mem sp0 regs0 Hsp Hlo Hhi Hew Hfr. unfold region_ok, lf_stackL.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Hsp.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (i & <- & Hi). apply in_seq in Hi.
pose proof (bv_unsigned_in_range 64 (getr regs0 (Z_to_bv 5 (nth i lf_saved 0)))) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
apply (chunk_ok_val SEGS E _ (sp0 - 80) (8 * Z.of_nat i) 8 (SOff (34 + i) 0) (bv_unsigned (getr regs0 (Z_to_bv 5 (nth i lf_saved 0))))).
- cbn [sv_denot]. rewrite (Hew i ltac:(lia)), Z.add_0_r, !Z_to_bv_bv_unsigned. reflexivity.
- change (8 * Z.of_N 8) with 64. exact Hr.
- cbn. lia.
- exact (Hfr i ltac:(lia)).
Qed.
(* the list's derived registers, with LA in atom a and the shadow base in atom b *)
Lemma lf_den_regs : forall E {a b : nat} LA, ew E a = Z_to_bv 64 LA -> ew E b = Z_to_bv 64 SB -> 0 <= LA < 2 ^ 60 ->
sv_denot E (SOff a 8) = Z_to_bv 64 (LA + 8) /\
sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff a 8) (SLit 3)) (SOff b 0)) = Z_to_bv 64 ((LA + 8) / 8 + SB) /\
sv_denot E (SAlu ALU_SRL (SOff a 0) (SLit 3)) = Z_to_bv 64 (LA / 8) /\
sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff a 0) (SLit 3)) (SOff b 0)) = Z_to_bv 64 (LA / 8 + SB).
Proof.
intros E a b LA H8 H18 HLA.
assert (U8 : forall c, 0 <= c <= 8 -> U E (SOff a c) = LA + c) by (intros c Hc; apply (U_atom_off E a LA c H8); lia).
assert (U18 : U E (SOff b 0) = SB) by (apply (U_atom E b SB H18); unfold SB; lia).
assert (Usrl : forall c, 0 <= c <= 8 -> U E (SAlu ALU_SRL (SOff a c) (SLit 3)) = (LA + c) / 8).
{ intros c Hc. rewrite U_SAlu. cbn [zalu_raw]. rewrite U8 by lia. rewrite U_SLit. change (Z.land (zcanon 3) 63) with 3.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. apply zcanon_id. unfold M64.
  split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
assert (D8 : 0 <= (LA + 8) / 8 < 2 ^ 60) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
assert (D0 : 0 <= LA / 8 < 2 ^ 60) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
split; [|split; [|split]]; rewrite denot_lit_U; f_equal.
- apply U8. lia.
- rewrite U_SAlu. cbn [zalu_raw]. rewrite Usrl by lia. rewrite U18. apply zcanon_id. unfold M64, SB. lia.
- rewrite Usrl by lia. rewrite Z.add_0_r. reflexivity.
- rewrite U_SAlu. cbn [zalu_raw]. rewrite Usrl by lia. rewrite U18, Z.add_0_r. apply zcanon_id. unfold M64, SB. lia.
Qed.
(* From the identity register map to lf_srL. *)
Lemma lf_set_srL : forall E pc rs fs regs m LA,
st_ok_pi SEGS VAL E (mkSS pc sr_atoms rs None fs) (mkst regs (Z_to_bv 64 (BASE + pc)) m (seg_rom SEGS)) ->
ew E 8 = Z_to_bv 64 LA -> ew E 18 = Z_to_bv 64 SB -> 0 <= LA < 2 ^ 60 ->
getr regs 9 = Z_to_bv 64 (LA + 8) -> getr regs 19 = Z_to_bv 64 ((LA + 8) / 8 + SB) ->
getr regs 20 = Z_to_bv 64 (LA / 8) -> getr regs 21 = Z_to_bv 64 (LA / 8 + SB) ->
st_ok_pi SEGS VAL E (mkSS pc lf_srL rs None fs) (mkst regs (Z_to_bv 64 (BASE + pc)) m (seg_rom SEGS)).
Proof.
intros E pc rs fs regs m LA H0 H8 H18 HLA R9 R19 R20 R21.
destruct (lf_den_regs E LA H8 H18 HLA) as (D9 & D19 & D20 & D21).
pose proof (ast_ok_pi_set_reg_fp E _ _ 9%bv (SOff 8 8) H0 eq_refl ltac:(rewrite D9; symmetry; exact R9)) as H1.
pose proof (ast_ok_pi_set_reg_fp E _ _ 19%bv _ H1 eq_refl ltac:(rewrite D19; symmetry; exact R19)) as H2.
pose proof (ast_ok_pi_set_reg_fp E _ _ 20%bv _ H2 eq_refl ltac:(rewrite D20; symmetry; exact R20)) as H3.
pose proof (ast_ok_pi_set_reg_fp E _ _ 21%bv _ H3 eq_refl ltac:(rewrite D21; symmetry; exact R21)) as H4.
exact H4.
Qed.
(* the shadow entry of the list struct, in any ARx state *)
Lemma lf_shent8_x : forall E ly S Hp W mem md LA,
ARx ly S Hp W mem md -> azs B LA 16 -> ew E 8 = Z_to_bv 64 LA -> ew E 18 = Z_to_bv 64 SB ->
0x10000 <= LA -> LA + 16 <= 0x5fb000 ->
shent_ok SEGS lf_BxL E (mrestrict (w_H W) mem) (mkSHE 8 0 16).
Proof.
intros E ly S Hp W mem md LA HAR HZS H8 H18 HL1 HL2.
apply (shent_ok_of_range SEGS (w_H W) mem E lf_BxL 8 LA 16 LA 0 16).
+ exact (azs_range_addressable_x B ARx LAWS ly S Hp W mem md LA 16 HAR HZS).
+ unfold lf_BxL. rewrite (U_atom E 18 SB H18) by (unfold SB; lia). reflexivity.
+ rewrite (U_atom E 8 LA H8) by lia. reflexivity.
+ lia.
+ lia.
+ intros x Hx. unfold SHADOW_OFF. cbn in Hx. lia.
Qed.
Lemma lf_aexpr_val : forall E c v, ew E 23 = Z_to_bv 64 c -> ew E 32 = Z_to_bv 64 v ->
1 <= c < 2 ^ 30 -> 0 <= v < 2 ^ 48 -> U E lf_aexpr = v + 16 * (c - 1).
Proof.
intros E c v H23 H32 Hc Hv. unfold lf_aexpr.
rewrite !U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 23 c H23) by lia. rewrite (U_atom E 32 v H32) by lia. rewrite !U_SLit.
assert (A4 : Z.land (zcanon 4) 63 = 4) by (vm_compute; reflexivity). rewrite A4.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
assert (Am16 : zcanon (-16) = 2 ^ 64 - 16) by (vm_compute; reflexivity). rewrite Am16.
unfold zcanon, M64. rewrite (Z.mod_small (c * 16)) by lia.
replace (c * 16 + (2 ^ 64 - 16)) with (16 * (c - 1) + 1 * 2 ^ 64) by lia.
rewrite Z_mod_plus_full. rewrite (Z.mod_small (16 * (c - 1))) by lia.
replace (16 * (c - 1) + v) with (v + 16 * (c - 1)) by lia. apply Z.mod_small. lia.
Qed.

Lemma lf_head_loop_x : forall W ly S Hp mem md regs regs0 LA v cap c s,
ARx ly S Hp W mem md -> lf_regs regs regs0 LA c -> lf_sp0 (spZ regs0) -> lf_frame W mem (spZ regs0) regs0 ->
0x10000 <= LA -> LA + 16 <= 0x5fb000 -> azs B LA 16 ->
val_mem SEGS (arm W mem) LA 8 v -> val_mem SEGS (arm W mem) (LA + 8) 4 c -> val_mem SEGS (arm W mem) (LA + 12) 4 cap ->
awr W mem LA 16 -> 1 <= c <= cap -> cap < 2 ^ 30 ->
In (v, AREC * cap) (ablocks B ly S) ->
val_mem SEGS (arm W mem) (v + 16 * (c - 1)) 8 s -> 0 <= s < 2 ^ 64 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (lf_xl v cap s (v + 16 * (c - 1)) regs0))) ss_lfL
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_lf_loop)) mem (seg_rom SEGS))) /\
sh_ok SEGS lf_BxL lf_SHL (Eimg (Ereg regs (lf_xl v cap s (v + 16 * (c - 1)) regs0))) (mrestrict (w_H W) mem).
Proof.
intros W ly S Hp mem md regs regs0 LA v cap c s HAR HR Hsp0 Hfr HL1 HL2 HZS Mv Mn Mc Hw Hc Hcap Hin Ms Rs.
destruct HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R21 & R23 & R25 & R26 & R27).
destruct Hsp0 as (Hal & Hsp1 & Hsp2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hin) as (Hv16 & Hv4096 & Hvce & Hvapp & _).
pose proof (blk_off_imgP_x B ARx LAWS IMGC BLKN _ _ _ _ _ _ _ _ HAR Hin) as Hvimg.
assert (Rq : req_size (AREC * cap) = 16 * cap) by (unfold req_size, AREC; destruct (Z.eqb_spec (16 * cap) 0); lia).
rewrite Rq in Hvce, Hvapp, Hvimg.
set (d := v + 16 * (c - 1)) in *.
assert (Hd16 : d mod 16 = 0) by (subst d; rewrite (Z.mul_comm 16 (c - 1)), Z_mod_plus_full; exact Hv16).
assert (Hsp80 : (spZ regs0 - 80) mod 16 = 0) by (rewrite Zminus_mod, Hal; reflexivity).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (lf_xl v cap s d regs0))).
assert (E2 : ew E 2 = Z_to_bv 64 (spZ regs0 - 80)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact R2).
assert (E8 : ew E 8 = Z_to_bv 64 LA) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 8 8%bv eq_refl); exact R8).
assert (E18 : ew E 18 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact R18).
assert (E23 : ew E 23 = Z_to_bv 64 c) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 23 23%bv eq_refl); exact R23).
assert (E32 : ew E 32 = Z_to_bv 64 v) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 cap) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E44 : ew E 44 = Z_to_bv 64 s) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 12)).
assert (E45 : ew E 45 = Z_to_bv 64 d) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 13)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs0 - 80) by (rewrite E2; apply unsigned_lit_small; lia).
assert (VB : forall m w, ew E m = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some m) = w).
{ intros m w Hm Hw'. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hw'. }
split.
- unfold ss_lfL. apply (lf_set_srL E A_lf_loop _ _ regs _ LA); [| exact E8 | exact E18 | lia | exact R9 | exact R19 | exact R20 | exact R21].
apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ constructor; [|constructor; [|constructor; [|constructor]]].
* apply (lf_stackL_ok E W mem (spZ regs0) regs0 Usp ltac:(lia) ltac:(lia)); [|exact Hfr].
intros i Hi. subst E. exact (lf_ew_saved regs regs0 v cap s d i Hi).
* apply (lf_lreg_ok E W mem 8 LA _ _ _ v c cap).
-- rewrite E8. apply unsigned_lit_small. lia.
-- lia.
-- lia.
-- cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
-- lia.
-- cbn [sv_denot]. rewrite E23, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
-- lia.
-- cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
-- lia.
-- exact Mv.
-- exact Mn.
-- exact Mc.
-- exact Hw.
* unfold region_ok, lf_slotL. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
rewrite (VB 45%nat d E45) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ d 0 8 (SOff 44 0) s); [cbn [sv_denot]; rewrite E44, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
rewrite Z.add_0_r. exact Ms.
+ apply pairwise_disjoint_of_extents. unfold lf_stackL, lf_lregL, lf_lreg, lf_slotL, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB 45%nat d E45) by lia. rewrite (VB 8%nat LA E8) by lia. cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hsp1 Hsp2 C1 HL1 HL2 Hvce Hvimg Hv4096 Hc. subst d. clear.
unfold off_img. intros. repeat split; lia.
+ assert (Hv48 : 0 <= v < 2 ^ 48) by (unfold alloc_ceiling in *; lia).
assert (Hc30 : 1 <= c < 2 ^ 30) by lia.
split; [|split; [exact I|]].
cbn [lf_atomsL app f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E8, E18, E23, E45, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hsp1 Hsp2 C1 HL1 HL2 Hvce Hv4096 Hc Hcap Hsp80 Hd16. subst d. clear.
unfold SB. intros. repeat match goal with |- _ /\ _ => split end; lia.
cbn [lf_atomsL app f_alias alias_ok]. split; [|exact I].
rewrite !denot_lit_U. f_equal.
rewrite (lf_aexpr_val E c v E23 E32 Hc30 Hv48). rewrite (U_atom E 45 d E45) by lia. reflexivity.
- unfold sh_ok, lf_SHL. constructor; [|constructor; [|constructor]].
+ exact (lf_shent8_x E ly S Hp W mem md LA HAR HZS E8 E18 HL1 HL2).
+ apply (shent_ok_of_range SEGS (w_H W) mem E lf_BxL 45 d 8 d 0 8).
* apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly S Hp W mem md v (AREC * cap) d 8 HAR Hin); [lia|]. rewrite Rq. lia.
* unfold lf_BxL. rewrite (U_atom E 18 SB E18) by (unfold SB; lia). reflexivity.
* rewrite (U_atom E 45 d E45) by lia. reflexivity.
* lia.
* lia.
* intros x Hx. cbn in Hx. revert Hvapp Hx Hc. subst d. clear. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg. intros. lia.
Qed.
Lemma lf_head_exit_x : forall W ly S Hp mem md regs regs0 LA v cap,
ARx ly S Hp W mem md -> lf_regsT regs regs0 LA -> lf_sp0 (spZ regs0) -> lf_frame W mem (spZ regs0) regs0 ->
0x10000 <= LA -> LA + 16 <= 0x5fb000 -> azs B LA 16 ->
val_mem SEGS (arm W mem) LA 8 v -> val_mem SEGS (arm W mem) (LA + 8) 4 0 -> val_mem SEGS (arm W mem) (LA + 12) 4 cap ->
awr W mem LA 16 -> 0 <= v < 2 ^ 64 -> 0 <= cap < 2 ^ 32 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (lf_xl v cap 0 0 regs0))) ss_lfX
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_lf_done)) mem (seg_rom SEGS))) /\
sh_ok SEGS lf_BxL lf_SHT (Eimg (Ereg regs (lf_xl v cap 0 0 regs0))) (mrestrict (w_H W) mem).
Proof.
intros W ly S Hp mem md regs regs0 LA v cap HAR HR Hsp0 Hfr HL1 HL2 HZS Mv Mn Mc Hw Hv Hcp.
destruct HR as (R2 & R3 & R4 & R8 & R18 & R20 & R25 & R26 & R27).
destruct Hsp0 as (Hal & Hsp1 & Hsp2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (Hsp80 : (spZ regs0 - 80) mod 16 = 0) by (rewrite Zminus_mod, Hal; reflexivity).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (lf_xl v cap 0 0 regs0))).
assert (E2 : ew E 2 = Z_to_bv 64 (spZ regs0 - 80)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact R2).
assert (E8 : ew E 8 = Z_to_bv 64 LA) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 8 8%bv eq_refl); exact R8).
assert (E18 : ew E 18 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact R18).
assert (E32 : ew E 32 = Z_to_bv 64 v) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 cap) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs0 - 80) by (rewrite E2; apply unsigned_lit_small; lia).
destruct (lf_den_regs E LA E8 E18 ltac:(lia)) as (_ & _ & D20 & _).
split.
- refine (ast_ok_pi_set_reg_fp E ss_lfX0 _ 20%bv (SAlu ALU_SRL (SOff 8 0) (SLit 3)) _ eq_refl _);
  [| cbn [ms_regs mkst]; rewrite D20; symmetry; exact R20].
  unfold ss_lfX0. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + constructor; [|constructor; [|constructor]].
    * apply (lf_stackL_ok E W mem (spZ regs0) regs0 Usp ltac:(lia) ltac:(lia)); [|exact Hfr].
      intros i Hi. subst E. exact (lf_ew_saved regs regs0 v cap 0 0 i Hi).
    * apply (lf_lreg_ok E W mem 8 LA _ _ _ v 0 cap).
      -- rewrite E8. apply unsigned_lit_small. lia.
      -- lia.
      -- lia.
      -- cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      -- exact Hv.
      -- reflexivity.
      -- lia.
      -- cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      -- exact Hcp.
      -- exact Mv.
      -- exact Mn.
      -- exact Mc.
      -- exact Hw.
  + apply pairwise_disjoint_of_extents. unfold lf_stackL, lf_lregX, lf_lreg, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    cbn [base_val]. rewrite Usp. rewrite E8, unsigned_lit_small by lia.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hsp1 Hsp2 C1 HL1 HL2. clear. intros. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [lf_factsX f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2, E8, E18, !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    revert Hsp1 Hsp2 C1 HL1 HL2 Hsp80. clear. unfold SB. intros. repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, lf_SHT. constructor; [|constructor].
  exact (lf_shent8_x E ly S Hp W mem md LA HAR HZS E8 E18 HL1 HL2).
Qed.
Lemma lf_firstn_last : forall {A} (l : list A) k d, (k < length l)%nat -> firstn (S k) l = firstn k l ++ [nth k l d].
Proof.
intros A l. induction l as [|x l IH]; intros k d Hk; [cbn in Hk; lia|]. destruct k as [|k]; [reflexivity|].
cbn [firstn nth]. rewrite (IH k d) by (cbn in Hk; lia). reflexivity.
Qed.

(* ---- the loop ---- *)
Definition lf_blks (l : hlist) (c : nat) : list (Z * Z) :=
(if hl_cap l =? 0 then [] else [(hl_v l, AREC * hl_cap l)]) ++
map (fun r => (fst r, Z.of_nat (length (snd r)) + 1)) (firstn c (hl_recs l)).
(* the state at the loop head (c texts left) or after the loop (c = 0) *)
Definition lf_inv_x (W : world SEGS) ly S (Hp : list Z) regs0 mem0 md0 (LA : Z) (l : hlist) (c kr : nat)
(Wc : world SEGS) lyc Sc (Hpc : list Z) (regs : bvmap 5 word) memc mdc (kk : Z) : Prop :=
ajournal_gx_x SEGS B PST ARx G 0 [] LF_STK (spZ regs0) (blk_FP (list_blks l)) ly S Hp W mem0 md0 [] lyc Sc Hpc Wc memc mdc kk /\
lf_regs regs regs0 LA (Z.of_nat c) /\ lf_frame Wc memc (spZ regs0) regs0 /\
val_mem SEGS (arm Wc memc) LA 8 (hl_v l) /\ val_mem SEGS (arm Wc memc) (LA + 8) 4 (Z.of_nat c) /\
val_mem SEGS (arm Wc memc) (LA + 12) 4 (hl_cap l) /\ awr Wc memc LA 16 /\
(0 < hl_cap l -> In (hl_v l, AREC * hl_cap l) (ablocks B lyc Sc) /\
  garr8 SEGS (arm Wc memc) (hl_v l) (bzs (concat (map text_rec (hl_recs l)) ++ hl_junk l))) /\
Forall (fun r => In (fst r, Z.of_nat (length (snd r)) + 1) (ablocks B lyc Sc)) (firstn c (hl_recs l)) /\
(forall rest, Permutation (ablocks B ly S) (list_blks l ++ rest) -> Permutation (ablocks B lyc Sc) (lf_blks l c ++ rest)) /\
frames Sc = frames S /\ mo_le MT S Sc ((hl_n l - Z.of_nat c) * mo_free MT) /\ apres_kept B W mem0 Wc memc /\
(forall i, 0 <= i < 4 -> aview SEGS (w_H Wc) memc (as_errno B + i) = aview SEGS (w_H W) mem0 (as_errno B + i)) /\
rp_RM RP Sc (c + 1 + kr) /\ cnt_ok RP (ablocks B lyc Sc).
Definition lf_ctx_x W ly S Hp regs0 mem0 md0 ch LA (l : hlist) lines : Prop :=
afn_pre_x SEGS B ARx LF_STK ly S Hp W regs0 mem0 md0 ch /\ alist_at B ly S W mem0 LA l lines /\
(forall a, LA <= a < LA + 16 -> inG G a) /\ azs B LA 16 /\ rom_view SEGS W mem0 /\ mo_ok MT S (lf_cost MT l).

Lemma lf_iter_x : forall (c : nat) W ly S Hp regs0 mem0 md0 ch LA (l : hlist) lines kr Wc lyc Sc Hpc regs memc mdc kk,
lf_ctx_x W ly S Hp regs0 mem0 md0 ch LA l lines -> (1 <= c <= length (hl_recs l))%nat ->
lf_inv_x W ly S Hp regs0 mem0 md0 LA l c kr Wc lyc Sc Hpc regs memc mdc kk ->
(forall Wc' lyc' Sc' Hpc' regs' memc' mdc' kk', lf_inv_x W ly S Hp regs0 mem0 md0 LA l (c - 1) kr Wc' lyc' Sc' Hpc' regs' memc' mdc' kk' ->
  SRr SEGS Wc' (mkCfg (mkst regs' (Z_to_bv 64 (BASE + if (c - 1 =? 0)%nat then A_lf_done else A_lf_loop)) memc' (seg_rom SEGS)) mdc')
  (lf_post_x B PST ARx MT RP G regs0 ly S Hp W mem0 md0 LA l lines kr)) ->
SRr SEGS Wc (mkCfg (mkst regs (Z_to_bv 64 (BASE + A_lf_loop)) memc (seg_rom SEGS)) mdc) (lf_post_x B PST ARx MT RP G regs0 ly S Hp W mem0 md0 LA l lines kr).
Proof.
intros c W ly S Hp regs0 mem0 md0 ch LA l lines kr Wc lyc Sc Hpc regs memc mdc kk HCTX Hc HINV HK.
destruct HCTX as (HPRE & HL & HLG & HZS & HROM & HMO).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof (lf_LA_range LA HLG) as (HLA1 & HLA2 & _ & _ & HLAe).
pose proof (lf_errno_facts (spZ regs0) LA ltac:(clear - Hceil Hslo; lia) HLG) as ERF.
destruct HINV as (HJ & HR & Hfr & Mv & Mn & Mc & Hw & HVEC & HTX & HPERM & HFRS & HMLE & HAPK & HERR & HRM & HCNT).
pose proof HL as (_ & _ & _ & _ & (Hn0 & Hcap) & Hvc & Hnd & Hnv & HFA).
assert (Hcap0 : 0 < hl_cap l) by (clear - Hc Hn0; unfold hl_n in Hn0; lia).
destruct (HVEC Hcap0) as (Hvin & Hvg).
pose proof (ajournal_gx_AR_x SEGS B PST ARx G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARc.
set (r := nth (c - 1) (hl_recs l) (0, [])).
assert (Hfl : firstn c (hl_recs l) = firstn (c - 1) (hl_recs l) ++ [r]).
{ subst r. clear -Hc. destruct c as [|c0]; [lia|]. cbn [Nat.sub]. rewrite Nat.sub_0_r. apply lf_firstn_last. lia. }
assert (Hrin : In r (firstn c (hl_recs l))) by (rewrite Hfl; apply in_or_app; right; left; reflexivity).
assert (Hrin' : In r (hl_recs l)) by (rewrite <- (firstn_skipn c (hl_recs l)); apply in_or_app; left; exact Hrin).
assert (Hrb : In (fst r, Z.of_nat (length (snd r)) + 1) (ablocks B lyc Sc)) by (exact (proj1 (Forall_forall _ _) HTX r Hrin)).
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HARc Hrb) as (Hs16 & Hs4096 & Hsce & _).
assert (Hsr : 4096 <= fst r /\ fst r + Z.of_nat (length (snd r)) + 1 <= alloc_ceiling).
{ clear - Hsce Hs4096. unfold req_size in Hsce. destruct (Z.eqb_spec (Z.of_nat (length (snd r)) + 1) 0); lia. }
pose proof (lf_slot_val _ _ _ _ (c - 1) Hvg ltac:(clear - Hc; lia)) as Ms. fold r in Ms.
rewrite unsigned_lit_small in Ms by (unfold alloc_ceiling in *; lia).
replace (16 * Z.of_nat (c - 1)) with (16 * (Z.of_nat c - 1)) in Ms by (clear - Hc; lia).
assert (Hsp0 : lf_sp0 (spZ regs0)) by (split; [exact Hal16 | clear - Hceil Hslo Hshi H47; unfold LF_STK, ASTACK in *; lia]).
assert (Hc1 : 1 <= Z.of_nat c <= hl_cap l) by (clear - Hc Hn0; unfold hl_n in Hn0; lia).
assert (Hsr64 : 0 <= fst r < 2 ^ 64) by (unfold alloc_ceiling in *; lia).
pose proof Hsp0 as (Hsp0a & Hsp0b & Hsp0c).
assert (Rq : req_size (AREC * hl_cap l) = 16 * hl_cap l) by (unfold req_size, AREC; destruct (Z.eqb_spec (16 * hl_cap l) 0); lia).
pose proof (blk_off_imgP_x B ARx LAWS IMGC BLKN _ _ _ _ _ _ _ _ HARc Hvin) as Hvimg. rewrite Rq in Hvimg. unfold off_img in Hvimg.
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HARc Hvin) as (Hv16 & Hv4096 & Hvce & _). rewrite Rq in Hvce.
assert (Hv64 : 0 <= hl_v l < 2 ^ 48) by (unfold alloc_ceiling in *; lia).
assert (Hjl : Z.of_nat (length (hl_junk l)) = AREC * (hl_cap l - hl_n l))
by (destruct Hvc as [[H0 _] | (_ & _ & Hj & _)]; [lia | exact Hj]).
assert (Hvlen : Z.of_nat (length (bzs (concat (map text_rec (hl_recs l)) ++ hl_junk l))) = 16 * hl_cap l).
{ unfold bzs. rewrite length_map, length_app, lf_len_text_recs. unfold hl_n, AREC in *. lia. }
assert (Hsv : fst r <> hl_v l) by (intros He; apply Hnv; rewrite <- He; apply in_map; exact Hrin').
assert (Hvne : (hl_v l, AREC * hl_cap l) <> (fst r, Z.of_nat (length (snd r)) + 1))
by (intros He; injection He as He1 _; exact (Hsv (eq_sym He1))).
assert (Dvs : hl_v l + 16 * hl_cap l <= fst r \/ fst r + req_size (Z.of_nat (length (snd r)) + 1) <= hl_v l).
{ pose proof (sep_blocks_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc _ _ _ _ HARc Hvin Hrb Hvne) as D. rewrite Rq in D.
  unfold zdisjoint in D. cbn [fst snd] in D. exact D. }
destruct (lf_head_loop_x Wc lyc Sc Hpc memc mdc regs regs0 LA (hl_v l) (hl_cap l) (Z.of_nat c) (fst r) HARc HR
  Hsp0 Hfr HLA1 HLA2 HZS Mv Mn Mc Hw Hc1 Hcap Hvin Ms Hsr64) as [HS SHOK].
remember (Eimg (Ereg regs (lf_xl (hl_v l) (hl_cap l) (fst r) (hl_v l + 16 * (Z.of_nat c - 1)) regs0))) as E eqn:HE in HS.
rewrite <- HE in SHOK.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
destruct HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R21 & R23 & R25 & R26 & R27).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs0 - 80).
{ rewrite E2, R2. apply unsigned_lit_small. destruct Hsp0 as (Hm & H1 & H2). unfold alloc_ceiling in H1. lia. }
assert (E3 : ew E 3 = getr regs0 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 3 3%bv eq_refl); exact R3).
assert (E4 : ew E 4 = getr regs0 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 4 4%bv eq_refl); exact R4).
assert (E25 : ew E 25 = getr regs0 25) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact R25).
assert (E26 : ew E 26 = getr regs0 26) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact R26).
assert (E27 : ew E 27 = getr regs0 27) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact R27).
assert (E8 : ew E 8 = Z_to_bv 64 LA) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 8 8%bv eq_refl); exact R8).
assert (E18 : ew E 18 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact R18).
assert (E23 : ew E 23 = Z_to_bv 64 (Z.of_nat c)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 23 23%bv eq_refl); exact R23).
assert (E32 : ew E 32 = Z_to_bv 64 (hl_v l)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (hl_cap l)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E44 : ew E 44 = Z_to_bv 64 (fst r)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 12)).
assert (E45 : ew E 45 = Z_to_bv 64 (hl_v l + 16 * (Z.of_nat c - 1))) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 13)).
assert (ESV : forall i, (i < 10)%nat -> ew E (34 + i) = getr regs0 (Z_to_bv 5 (nth i lf_saved 0)))
by (intros i Hi; subst E; exact (lf_ew_saved regs regs0 _ _ _ _ i Hi)).
assert (U8 : bv_unsigned (ew E 8) = LA) by (rewrite E8; apply unsigned_lit_small; lia).
assert (HAE : env_agree 32 (Ereg regs (lf_xl (hl_v l) (hl_cap l) (fst r) (hl_v l + 16 * (Z.of_nat c - 1)) regs0)) E)
by (subst E; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HMLE' : mo_le MT S Sc ((hl_n l - Z.of_nat c) * mo_free MT)) by exact HMLE.
assert (HMOf : mo_ok MT Sc (mo_free MT)).
{ eapply (mok_station MT S Sc (lf_cost MT l) _ (mo_free MT) MLAW HMO HMLE'); [pose proof (mo_free_nonneg MT MLAW); lia|].
  unfold lf_cost, hl_n. pose proof (mo_free_nonneg MT MLAW) as Hf.
  assert (Hcn : Z.of_nat c <= Z.of_nat (length (hl_recs l))) by (clear - Hc Hn0; unfold hl_n in Hn0; lia).
  clear - Hf Hcn. nia. }
paj_run_tok_x RUN HS HJ SHOK lf_Bspan.
{ apply awr_ok_x_cons_awr0; [awr_ok_tac; exact Usp|]. apply awr_ok_x_cons_g; [|apply awr_ok_x_cons_awr0; [awr_ok_tac|apply awr_ok_x_nil]].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi lf_lregL lf_lreg base_val]. subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs _ 8 8%bv eq_refl), R8, unsigned_lit_small by lia. intros a Ha. apply HLG. lia. }
(* free(v[c-1].s) *)
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.
destruct HJ as (HSTK & HXO & (memS & HJi & Hag) & Hout). rewrite !Z.add_0_r in HJi.
pose proof (proj1 HJi) as HARm.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (LA <= a < LA + 16) -> aview SEGS (w_H Wc) (ms_mem ms) a = aview SEGS (w_H Wc) memc a).
{ intros a Ha Hno. lazymatch goal with Hf : frame_of _ _ (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) (ms_mem ms)) |- _ =>
    apply (aview_kept_out _ _ (w_H Wc) memc (ms_mem ms) Hf a Ha) end.
  intros (rg & Hin & Hr). cbn [ss_mem ss_lfL In] in Hin. destruct Hin as [<- | [<- | [<- | []]]];
  cbn [lf_stackL lf_lregL lf_lreg lf_slotL YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr;
  [lia | rewrite U8 in Hr; lia | lia]. }
assert (Usp2 : spZ (ms_regs ms) = spZ regs0 + -80).
{ unfold spZ at 1. rewrite Q2. rewrite Usp. lia. }
assert (R10s : getr (ms_regs ms) 10 = w64 (fst r)).
{ rewrite Q10. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 12). }
assert (HGP : getr (ms_regs ms) 3 = w64 (as_gp B)).
{ rewrite Q3. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 3 3%bv eq_refl), R3. exact Hgp. }
assert (HTP : getr (ms_regs ms) 4 = w64 (as_tp B)).
{ rewrite Q4. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 4 4%bv eq_refl), R4. exact Htp. }
assert (HS0 : s0Z (ms_regs ms) = LA).
{ unfold s0Z. rewrite Q8. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 8 8%bv eq_refl), R8. apply unsigned_lit_small. lia. }
assert (HCH : chain_pre lyc (aview SEGS (w_H Wc) (ms_mem ms)) (ms_regs ms) []).
{ unfold chain_pre. split; [unfold raZ; rewrite Q1; rewrite unsigned_lit_small by lia; lia|].
  destruct (frame0_ok lyc (ms_regs ms)); [|reflexivity].
  replace (bad_next (spZ (ms_regs ms)) (ly_top lyc) (s0Z (ms_regs ms))) with true; [reflexivity|].
  symmetry. unfold bad_next. rewrite HS0, Usp2. apply orb_true_iff. left. apply orb_true_iff. left. apply Z.leb_le. lia. }
(* the free's caller context: the chain is [] (s0 = LA, an image address), the trace the singleton [list_free + 0x98] *)
assert (HCTXL : In (raZ (ms_regs ms) :: spine []) CTX).
{ cbn [spine map]. replace (raZ (ms_regs ms)) with (BASE + AF_fr_list_free + 0x98); [exact HCTX_lf_loop|].
  unfold raZ. rewrite Q1, unsigned_lit_small by lia. first [lia | unfold AF_fr_list_free in *; lia]. }
rewrite HBfree.
assert (HRMc : rp_RM RP Sc (1 + (c - 1 + 1 + kr))) by (apply (lf_rm_cast RP Sc _ _ HRM); clear - Hc; lia).
eapply SRr_bind.
{ exact (AFREE Wc (ms_regs ms) (ms_mem ms) LF_STK (spZ regs0) (blk_FP (list_blks l)) ly S Hp W memS md0 [] lyc Sc Hpc _ _
      (fst r) (Z.of_nat (length (snd r)) + 1) (-80) (getr (ms_regs ms) 1) [] (c - 1 + 1 + kr)%nat HJi Hrb R10s Usp2 eq_refl ltac:(lia)
      ltac:(unfold LF_STK, ASTACK; lia)
      (aj_stack_room_x SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (-80) (ms_regs ms) HJi Usp2 ltac:(unfold LF_STK, ASTACK; lia))
      HGP HTP eq_refl ltac:(rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]) HCH HCTXL
      HRMc HCNT
      ltac:(intros _ i Hi; apply (inFP_ablocks_fp (list_blks l) (fst r) (Z.of_nat (length (snd r)) + 1) i);
            [unfold list_blks; apply in_or_app; right; apply (in_map (fun r0 => (fst r0, Z.of_nat (length (snd r0)) + 1))); exact Hrin' | exact Hi]) HMOf). }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & -> & HJ2i & HP2 & (b1 & b2 & Eb1 & Eb2) & HFR2 & HK2 & HML2 & HRM2 & HER2 & HPR2).
rewrite Q1.
pose proof (proj1 HJ2i) as HAR2.
assert (HJ2 : ajournal_gx_x SEGS B PST ARx G 0 [] LF_STK (spZ regs0) (blk_FP (list_blks l)) ly S Hp W mem0 md0 [] ly2 S2 Hp2 W2 mem2 md2 (kk + 1)).
{ apply (ajournal_gx_pack_x SEGS B PST ARx G 0 [] LF_STK (spZ regs0) _ ly S Hp W mem0 md0 [] ly2 S2 Hp2 W2 mem2 md2 (kk + 1) memS HSTK HXO);
  [rewrite !Z.add_0_r; exact HJ2i | exact Hag | apply out_none]. }
(* ---- the bookkeeping of the free: the vector and the other texts stay, the text r goes ---- *)
assert (Hvin2 : In (hl_v l, AREC * hl_cap l) (ablocks B ly2 S2)) by (rewrite Eb2; exact (lf_in_drop _ _ b1 b2 _ Eb1 Hvin Hvne)).
assert (HndL : List.NoDup (map fst (hl_recs l))) by (apply (proj1 (stdpp.base.NoDup_ListNoDup _)); exact Hnd).
assert (Hnr : ~ In (fst r) (map fst (firstn (c - 1) (hl_recs l)))).
{ rewrite <- (firstn_skipn c (hl_recs l)) in HndL. rewrite map_app in HndL. apply List.NoDup_app_remove_r in HndL.
  rewrite Hfl, map_app in HndL. cbn [map] in HndL. intros Hin.
  apply (List.NoDup_remove_2 (map fst (firstn (c - 1) (hl_recs l))) [] (fst r)); [exact HndL | rewrite app_nil_r; exact Hin]. }
assert (HTX2 : Forall (fun r0 => In (fst r0, Z.of_nat (length (snd r0)) + 1) (ablocks B ly2 S2)) (firstn (c - 1) (hl_recs l))).
{ rewrite Forall_forall in HTX |- *. intros r0 Hr0. rewrite Eb2. apply (lf_in_drop _ _ b1 b2 _ Eb1).
  - apply HTX. rewrite Hfl. apply in_or_app. left. exact Hr0.
  - intros He. injection He as He1 _. apply Hnr. rewrite <- He1. apply in_map. exact Hr0. }
assert (HPERM2 : forall rest, Permutation (ablocks B ly S) (list_blks l ++ rest) ->
  Permutation (ablocks B ly2 S2) (lf_blks l (c - 1) ++ rest)).
{ intros rest Hpp. pose proof (HPERM rest Hpp) as Hp1. rewrite Eb1 in Hp1. rewrite Eb2.
  unfold lf_blks in Hp1 |- *. rewrite Hfl, map_app in Hp1. cbn [map] in Hp1.
  exact (lf_perm_drop2 b1 b2 _ _ rest _ Hp1). }
assert (HML2' : mo_le MT S S2 ((hl_n l - Z.of_nat (c - 1)) * mo_free MT)).
{ assert (E1c : Z.of_nat (c - 1) = Z.of_nat c - 1) by (clear - Hc; lia). rewrite E1c.
  replace ((hl_n l - (Z.of_nat c - 1)) * mo_free MT) with ((hl_n l - Z.of_nat c) * mo_free MT + mo_free MT) by ring.
  exact (mle_station MT S Sc S2 _ _ MLAW HMLE' HML2). }
assert (HFRS2 : frames S2 = frames S) by (rewrite HFR2; exact HFRS).
assert (HCNT2 : cnt_ok RP (ablocks B ly2 S2)).
{ rewrite Eb2. apply (lf_cnt_del RP b1 (fst r, Z.of_nat (length (snd r)) + 1) b2). rewrite <- Eb1. exact HCNT. }
lazymatch goal with Hgr : mem_grows (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) (ms_mem ms)) |- _ =>
  assert (PR1 : forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) (ms_mem ms) a)
  by (intros a Hpp; exact (lf_apresent_grows (w_H Wc) memc (ms_mem ms) a Hgr Hpp)) end.
assert (HAPK2 : apres_kept B W mem0 W2 mem2).
{ intros a Hi Hno Herr Hpp.
  assert (Hnot : forall ly0 S0 Hp0 (W0 : world SEGS) m0 md0', ARx ly0 S0 Hp0 W0 m0 md0' -> ~ aowned B ly0 S0 a)
  by (intros ly0 S0 Hp0 W0 m0 md0' HA Ho; apply Hno; exact (proj1 (alx_owned_image _ _ _ LAWS ly0 S0 Hp0 W0 m0 md0' a HA Hi) Ho)).
  apply (HPR2 a Hi (Hnot _ _ _ _ _ _ HARm) (Hnot _ _ _ _ _ _ HAR2) Herr); [|exact (PR1 a (HAPK a Hi Hno Herr Hpp))].
  intros Hb. exact (blk_img_x SEGS B ARx LAWS lyc Sc Hpc Wc (ms_mem ms) _ _ _ a HARm Hrb Hb Hi). }
(* ---- after the free: keep the frame and the list struct (no slot) ---- *)
assert (HLAimg : forall a, LA <= a < LA + 16 ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4))
by (intros a Ha; exact (conj (proj1 (HG a (HLG a Ha))) (conj (proj1 (proj2 (HG a (HLG a Ha)))) (proj1 (HGR a (HLG a Ha)))))).
assert (KF : forall a, LA <= a < LA + 16 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) (ms_mem ms) a).
{ intros a Ha. destruct (HLAimg a Ha) as (Hi & Ho & He). destruct HK2 as (_ & _ & K3 & _). exact (K3 a Hi Ho He). }
assert (KFs : forall a, spZ regs0 - 80 <= a < spZ regs0 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) (ms_mem ms) a).
{ intros a Ha. destruct HK2 as (Kh & _). apply Kh; [destruct Hsp0 as (_ & H1 & H2); lia | lia]. }
assert (KFw : forall a, LA <= a < LA + 16 ->
  writable_at SEGS (mrestrict (w_H Wc) (ms_mem ms)) a -> writable_at SEGS (mrestrict (w_H W2) mem2) a).
{ intros a Ha. destruct (HLAimg a Ha) as (Hi & Ho & He). apply (lf_writable_img Wc W2 (ms_mem ms) mem2 a Hi).
  intros Hpp. apply (HPR2 a Hi); [| | exact He | | exact Hpp].
  - intros Hao. apply Ho. exact (proj1 (alx_owned_image _ _ _ LAWS _ _ _ _ _ _ a HARm Hi) Hao).
  - intros Hao. apply Ho. exact (proj1 (alx_owned_image _ _ _ LAWS _ _ _ _ _ _ a HAR2 Hi) Hao).
  - intros Hb. exact (blk_img_x SEGS B ARx LAWS lyc Sc Hpc Wc (ms_mem ms) _ _ _ a HARm Hrb Hb Hi). }
jafter_call_keep_pi HS 46%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0; 1]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - apply (lf_region_kept2 E Wc W2 (ms_mem ms) mem2 2 (spZ regs0 - 80)); [exact Usp | intros a Ha; apply KFs; lia | intros a Ha; exfalso; lia].
  - apply (lf_region_kept2 E Wc W2 (ms_mem ms) mem2 8 LA); [exact U8 | intros a Ha; apply KF; lia | intros a Ha; apply KFw; lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 46 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 46)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
clear HEa.
assert (SHOK2 : sh_ok SEGS lf_BxL lf_SHT Ea (mrestrict (w_H W2) mem2)).
{ unfold sh_ok, lf_SHT. constructor; [|constructor].
  apply (lf_shent8_x Ea ly2 S2 Hp2 W2 mem2 md2 LA HAR2 HZS); [rewrite OLDa by lia; exact E8 | rewrite OLDa by lia; exact E18 | exact HLA1 | exact HLA2]. }
assert (Uspa : bv_unsigned (ew Ea 2) = spZ regs0 - 80) by (rewrite OLDa by lia; exact Usp).
assert (U8a : bv_unsigned (ew Ea 8) = LA) by (rewrite OLDa by lia; exact U8).
(* ---- 0x86118 .. the jal to __asan_memmove ---- *)
paj_run_tok_x RUN HS HJ2 SHOK2 lf_Bspan.
{ apply awr_ok_x_cons_awr0; [awr_ok_tac; exact Uspa|]. apply awr_ok_x_cons_g; [|apply awr_ok_x_nil].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]. rewrite U8a. intros a Ha. apply HLG. lia. }
lazymatch goal with |- SRr _ _ (mkCfg ?mm _) _ => rename mm into ms2 end.
lazymatch goal with Hgr : mem_grows (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) (ms_mem ms2)) |- _ =>
  assert (PR2 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms2) a)
  by (intros a Hpp; exact (lf_apresent_grows (w_H W2) mem2 (ms_mem ms2) a Hgr Hpp)) end.
lazymatch goal with Hf : frame_of _ _ (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) (ms_mem ms2)) |- _ => rename Hf into HFr2 end.
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (LA <= a < LA + 16) -> aview SEGS (w_H W2) (ms_mem ms2) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hno. apply (aview_kept_out _ _ (w_H W2) mem2 (ms_mem ms2) HFr2 a Ha).
  intros (rg & Hin & Hr). cbn [In] in Hin. destruct Hin as [<- | [<- | []]];
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr; [lia | rewrite U8a in Hr; lia]. }
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
pose proof (ajournal_gx_AR_x SEGS B PST ARx G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2m.
assert (Usp3 : spZ (ms_regs ms2) = spZ regs0 + -80) by (unfold spZ at 1; rewrite P2, Uspa; lia).
assert (HGP2 : getr (ms_regs ms2) 3 = w64 (as_gp B)) by (rewrite P3, OLDa by lia; rewrite E3; exact Hgp).
assert (HTP2 : getr (ms_regs ms2) 4 = w64 (as_tp B)) by (rewrite P4, OLDa by lia; rewrite E4; exact Htp).
assert (HROM2 : rom_view SEGS W2 (ms_mem ms2))
by (exact (ajournal_gx_rom_view_x SEGS B PST ARx LAWS pa_segs_low G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 HRO PSTR HROM)).
(* __asan_memmove(v + 16 (c - 1), v + 16 c, 0) *)
eapply SRr_bind.
{ apply (aj_gx_entry_at_x B PST ARx LAWS G 0 [] ESTACK (SIGMA WS_asan_memmove)
    (fun a => hl_v l + 16 * (Z.of_nat c - 1) <= a < hl_v l + 16 * (Z.of_nat c - 1) + 0)
    (fun regs' mem' => getr regs' 10 = w64 (hl_v l + 16 * (Z.of_nat c - 1)) /\
       forall i, 0 <= i < 0 -> aview SEGS (w_H W2) mem' (hl_v l + 16 * (Z.of_nat c - 1) + i) =
         aview SEGS (w_H W2) (ms_mem ms2) (hl_v l + 16 * (Z.of_nat c - 1) + 16 + i))
    W2 (ms_regs ms2) (ms_mem ms2) LF_STK (spZ regs0) (blk_FP (list_blks l)) ly S Hp W mem0 md0 [] ly2 S2 Hp2 _ (kk + 1) (-80) (getr (ms_regs ms2) 1) HG eq_refl HJ2).
  - exact Usp3.
  - reflexivity.
  - lia.
  - unfold ESTACK. lia.
  - unfold ESTACK, LF_STK, ASTACK. lia.
  - exact HGP2.
  - exact HTP2.
  - reflexivity.
  - rewrite P1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a. right. cbv beta. lia.
  - intros a Ha. exfalso. cbv beta in Ha. lia.
  - intros a Ha. exfalso. cbv beta in Ha. lia.
  - intros HPRE2 HSC2.
    exact (AMOVE ly2 S2 Hp2 W2 (ms_regs ms2) (ms_mem ms2) _ (hl_v l + 16 * (Z.of_nat c - 1)) (hl_v l + 16 * (Z.of_nat c - 1) + 16) 0 HPRE2
      ltac:(rewrite P10, OLDa by lia; exact E45)
      ltac:(rewrite P11, OLDa by lia; rewrite E45, unsigned_lit_small by (unfold alloc_ceiling in *; lia); reflexivity)
      ltac:(rewrite P12; reflexivity)
      ltac:(lia) ltac:(unfold alloc_ceiling in *; lia) ltac:(unfold alloc_ceiling in *; lia)
      ltac:(intros a Ha; exfalso; lia)
      ltac:(eapply (YCe5x.amem_range_of_block_x SEGS B ARx LAWS ly2 S2 Hp2 W2 (ms_mem ms2) _ (hl_v l) (AREC * hl_cap l)); [exact HAR2m | exact Hvin2 | lia | rewrite Rq; lia])
      ltac:(intros y Hy; exfalso; lia) ltac:(intros H0; exfalso; lia)
      ltac:(lia) ltac:(unfold alloc_ceiling in *; lia)
      ltac:(intros a Ha; exfalso; lia)
      ltac:(eapply (YCe5x.amem_range_of_block_x SEGS B ARx LAWS ly2 S2 Hp2 W2 (ms_mem ms2) _ (hl_v l) (AREC * hl_cap l)); [exact HAR2m | exact Hvin2 | lia | rewrite Rq; lia])
      ltac:(intros y Hy; exfalso; lia) ltac:(intros H0; exfalso; lia)
      HROM2 ltac:(intros H0; exfalso; lia) ltac:(intros a Ha; exfalso; lia)). }
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & (Hd10 & _) & Hfr3 & Hpres3).
rewrite P1.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs0 - 80 - ESTACK <= a < spZ regs0 - 80) ->
  aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) (ms_mem ms2) a).
{ intros a Ha Hs. apply Hfr3; [exact Ha | cbv beta; lia | lia]. }
jafter_call_keep_pi HS 62%nat regs3 (mrestrict (w_H W2) mem3) HP3 [0; 1]%nat HS3.
match type of HS3 with ?ty -> _ => assert (HRK : ty); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - apply (region_kept_aview Ea (w_H W2) (ms_mem ms2) mem3 2 (spZ regs0 - 80)); [exact Uspa | | exact Hpres3].
    intros a Ha. apply KM; [destruct Hsp0 as (_ & H1 & H2); unfold alloc_ceiling in H1; lia | unfold ESTACK; lia].
  - apply (region_kept_aview Ea (w_H W2) (ms_mem ms2) mem3 8 LA); [exact U8a | | exact Hpres3].
    intros a Ha. apply KM; [lia | destruct Hsp0 as (_ & H1 & H2); unfold alloc_ceiling, ESTACK in *; lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc Ea 62 (map (getr regs3) CLOB)) as Eb eqn:HEb in HS.
assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEIa | cbv; lia]).
assert (OLDb : forall m, (m < 62)%nat -> ew Eb m = ew Ea m) by (intros m Hm; rewrite HEb; apply YN3v.ew_havoc_old; exact Hm).
clear HEb.
pose proof (ajournal_gx_AR_x SEGS B PST ARx G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR3.
assert (SHOK3 : sh_ok SEGS lf_BxL lf_SHT Eb (mrestrict (w_H W2) mem3)).
{ unfold sh_ok, lf_SHT. constructor; [|constructor].
  apply (lf_shent8_x Eb ly2 S2 Hp2 W2 mem3 md3 LA HAR3 HZS);
  [rewrite OLDb, OLDa by lia; exact E8 | rewrite OLDb, OLDa by lia; exact E18 | exact HLA1 | exact HLA2]. }
assert (Uspb : bv_unsigned (ew Eb 2) = spZ regs0 - 80) by (rewrite OLDb by lia; exact Uspa).
assert (U8b : bv_unsigned (ew Eb 8) = LA) by (rewrite OLDb by lia; exact U8a).
(* ---- 0x86144 .. the bnez: l->n = c - 1 ---- *)
paj_run_tok_x RUN HS HJ3 SHOK3 lf_Bspan.
{ apply awr_ok_x_cons_awr0; [awr_ok_tac; exact Uspb|]. apply awr_ok_x_cons_g; [|apply awr_ok_x_nil].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]. rewrite U8b. intros a Ha. apply HLG. lia. }
lazymatch goal with |- SRr _ _ (mkCfg ?mm _) _ => rename mm into ms3 end.
lazymatch goal with Hf : frame_of _ _ (mrestrict (w_H W2) mem3) (mrestrict (w_H W2) (ms_mem ms3)) |- _ => rename Hf into HFr3 end.
lazymatch goal with Hgr : mem_grows (mrestrict (w_H W2) mem3) (mrestrict (w_H W2) (ms_mem ms3)) |- _ =>
  assert (PR3 : forall a, apresent (w_H W2) mem3 a -> apresent (w_H W2) (ms_mem ms3) a)
  by (intros a Hpp; exact (lf_apresent_grows (w_H W2) mem3 (ms_mem ms3) a Hgr Hpp)) end.
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (LA <= a < LA + 16) -> aview SEGS (w_H W2) (ms_mem ms3) a = aview SEGS (w_H W2) mem3 a).
{ intros a Ha Hno. apply (aview_kept_out _ _ (w_H W2) mem3 (ms_mem ms3) HFr3 a Ha).
  intros (rg & Hin & Hr). cbn [In] in Hin. destruct Hin as [<- | [<- | []]];
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr; [lia | rewrite U8b in Hr; lia]. }
(* the vector's bytes are the ones at the loop head *)
assert (VEC : forall a, hl_v l <= a < hl_v l + 16 * hl_cap l -> aview SEGS (w_H W2) (ms_mem ms3) a = aview SEGS (w_H Wc) memc a).
{ intros a Ha. assert (HnLA : ~ (LA <= a < LA + 16)) by lia.
  rewrite K3 by (first [exact HnLA | unfold alloc_ceiling in *; lia]).
  rewrite KM by (unfold ESTACK, LF_STK, ASTACK in *; lia).
  rewrite K2 by (first [exact HnLA | unfold alloc_ceiling in *; lia]).
  replace a with (hl_v l + (a - hl_v l)) by ring.
  destruct HK2 as (_ & KB & _). rewrite (KB (hl_v l) (AREC * hl_cap l) (a - hl_v l) Hvin) by (rewrite ?Rq; cbv beta; lia).
  replace (hl_v l + (a - hl_v l)) with a by ring. apply K1; [unfold alloc_ceiling in *; lia | exact HnLA]. }
assert (PRS : apres_kept B W mem0 W2 (ms_mem ms3)).
{ intros a Hi Hno Herr Hpp. apply PR3. apply Hpres3. apply PR2. exact (HAPK2 a Hi Hno Herr Hpp). }
assert (ERR3 : forall i, 0 <= i < 4 -> aview SEGS (w_H W2) (ms_mem ms3) (as_errno B + i) = aview SEGS (w_H W) mem0 (as_errno B + i)).
{ intros i Hi. rewrite K3 by lf_err_side ERF i Hi. rewrite KM by lf_err_side ERF i Hi. rewrite K2 by lf_err_side ERF i Hi.
  rewrite (HER2 i Hi). rewrite K1 by lf_err_side ERF i Hi. exact (HERR i Hi). }
assert (EB8 : ew Eb 8 = Z_to_bv 64 LA) by (rewrite OLDb, OLDa by lia; exact E8).
assert (EB18 : ew Eb 18 = Z_to_bv 64 SB) by (rewrite OLDb, OLDa by lia; exact E18).
assert (EB23 : ew Eb 23 = Z_to_bv 64 (Z.of_nat c)) by (rewrite OLDb, OLDa by lia; exact E23).
assert (EB32 : ew Eb 32 = Z_to_bv 64 (hl_v l)) by (rewrite OLDb, OLDa by lia; exact E32).
assert (EB33 : ew Eb 33 = Z_to_bv 64 (hl_cap l)) by (rewrite OLDb, OLDa by lia; exact E33).
destruct (lf_den_regs Eb LA EB8 EB18 ltac:(lia)) as (_ & D19 & D20 & D21).
psrr_branch_tok RUN BR HS SHOK3 lf_Bspan.
- (* c - 1 <> 0: back to the loop head *)
  lazymatch goal with Hb : branch_taken _ _ _ = true |- _ => rename Hb into Hbr end.
  rewrite branch_ne_U in Hbr.
  rewrite (U_atom_off Eb 23 (Z.of_nat c) (-1) EB23) in Hbr by lia.
  rewrite U_SLit, (zcanon_id 0) in Hbr by (unfold M64; lia).
  apply Bool.negb_true_iff, Z.eqb_neq in Hbr.
  assert (Hc0 : (c - 1 =? 0)%nat = false) by (apply Nat.eqb_neq; lia).
  rewrite Hc0 in HK.
  paj_run_to_tok_x RUNTO HS HJ3 SHOK3 lf_Bspan A_lf_loop.
  { lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
    apply awr_ok_x_cons_awr0; [awr_ok_tac; exact Uspb|]. apply awr_ok_x_cons_g; [|apply awr_ok_x_nil].
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]. rewrite U8b. intros a Ha. apply HLG. lia. }
  lazymatch goal with |- SRr _ _ (mkCfg ?mm _) _ => rename mm into msf end.
  lazymatch goal with Hf : frame_of _ _ (mrestrict (w_H W2) (ms_mem ms3)) (mrestrict (w_H W2) (ms_mem msf)) |- _ => rename Hf into HFr4 end.
  lazymatch goal with Hgr : mem_grows (mrestrict (w_H W2) (ms_mem ms3)) (mrestrict (w_H W2) (ms_mem msf)) |- _ => rename Hgr into HGr4 end.
  lazymatch type of HFr4 with frame_of ?Ev ?rs _ _ => let rs' := eval vm_compute in rs in change rs with rs' in HFr4 end.
  assert (K4 : forall a, 0 <= a < 2 ^ 64 -> ~ (LA <= a < LA + 16) -> aview SEGS (w_H W2) (ms_mem msf) a = aview SEGS (w_H W2) (ms_mem ms3) a).
  { intros a Ha Hno. apply (aview_kept_out _ _ (w_H W2) (ms_mem ms3) (ms_mem msf) HFr4 a Ha).
    intros (rg & Hin & Hr). cbn [In] in Hin. destruct Hin as [<- | [<- | []]];
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr; [lia | rewrite U8b in Hr; lia]. }
  pmkst HS.
  prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4. prreg HS (8%bv : bv 5) F8.
  prreg HS (9%bv : bv 5) F9. prreg HS (18%bv : bv 5) F18. prreg HS (23%bv : bv 5) F23.
  prreg HS (25%bv : bv 5) F25. prreg HS (26%bv : bv 5) F26. prreg HS (27%bv : bv 5) F27.
  prreg_raw HS (19%bv : bv 5) F19. prreg_raw HS (20%bv : bv 5) F20. prreg_raw HS (21%bv : bv 5) F21.
  pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RS0.
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RL1.
  cbn [ms_mem restrict] in RS0, RL1.
  assert (VL0 : val_mem SEGS (mrestrict (w_H W2) (ms_mem msf)) (LA + 0) (N.to_nat 8) (hl_v l)).
  { eapply (field_of_region Eb _ 8 LA); [exact RL1 | exact U8b | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
    cbn [sv_denot]. rewrite EB32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
  assert (VL8 : val_mem SEGS (mrestrict (w_H W2) (ms_mem msf)) (LA + 8) (N.to_nat 4) (Z.of_nat (c - 1))).
  { eapply (field_of_region Eb _ 8 LA); [exact RL1 | exact U8b | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
    cbn [sv_denot]. rewrite EB23, unsigned_lit_small by lia. f_equal. lia. }
  assert (VL12 : val_mem SEGS (mrestrict (w_H W2) (ms_mem msf)) (LA + 12) (N.to_nat 4) (hl_cap l)).
  { eapply (field_of_region Eb _ 8 LA); [exact RL1 | exact U8b | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
    cbn [sv_denot]. rewrite EB33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
  rewrite Z.add_0_r in VL0.
  assert (HAWR : awr W2 (ms_mem msf) LA 16).
  { intros i Hi. destruct RL1 as (_ & _ & RLw & _). cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in RLw.
    rewrite U8b in RLw. exact (RLw i Hi). }
  assert (HVEC' : 0 < hl_cap l -> In (hl_v l, AREC * hl_cap l) (ablocks B ly2 S2) /\
    garr8 SEGS (arm W2 (ms_mem msf)) (hl_v l) (bzs (concat (map text_rec (hl_recs l)) ++ hl_junk l))).
  { intros _. split; [exact Hvin2|]. unfold arm in Hvg |- *.
    apply (lf_garr8_kept (w_H Wc) (w_H W2) memc (ms_mem msf)); [|exact Hvg].
    intros j Hj. rewrite Hvlen in Hj. rewrite K4 by (unfold alloc_ceiling in *; lia). apply VEC. lia. }
  eapply (HK W2 ly2 S2 Hp2 (ms_regs msf) (ms_mem msf) _ (kk + 1)).
  unfold lf_inv_x.
  split; [exact HJ3|].
  split.
  { unfold lf_regs.
    split; [rewrite F2, OLDb, OLDa by lia; rewrite E2; exact R2|].
    split; [rewrite F3, OLDb, OLDa by lia; exact E3|].
    split; [rewrite F4, OLDb, OLDa by lia; exact E4|].
    split; [rewrite F8, OLDb, OLDa by lia; exact E8|].
    split; [rewrite F9, U8b; reflexivity|].
    split; [rewrite F18, OLDb, OLDa by lia; exact E18|].
    split; [rewrite F19; exact D19|].
    split; [rewrite F20; exact D20|].
    split; [rewrite F21; exact D21|].
    split; [rewrite F23, EB23, unsigned_lit_small by lia; f_equal; lia|].
    split; [rewrite F25, OLDb, OLDa by lia; exact E25|].
    split; [rewrite F26, OLDb, OLDa by lia; exact E26|].
    rewrite F27, OLDb, OLDa by lia; exact E27. }
  split.
  { intros i Hi. unfold arm.
    pose proof (bv_unsigned_in_range 64 (getr regs0 (Z_to_bv 5 (nth i lf_saved 0)))) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
    eapply (slot_of_region Eb _ (spZ regs0 - 80) _ 0 80 0 0 (8 * Z.of_nat i) (SOff (34 + i) 0)).
    - exact RS0.
    - exact Uspb.
    - clear - Hi. do 10 (destruct i as [|i]; [cbn [In]; repeat first [left; reflexivity | right] |]). lia.
    - cbn [sv_denot]. rewrite OLDb, OLDa by lia. rewrite (ESV i Hi), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    - exact Hr. }
  split; [exact VL0|]. split; [exact VL8|]. split; [exact VL12|]. split; [exact HAWR|]. split; [exact HVEC'|].
  split; [exact HTX2|]. split; [exact HPERM2|]. split; [exact HFRS2|]. split; [exact HML2'|].
  split; [intros a Hi Hno Herr Hpp; apply (lf_apresent_grows _ _ _ a HGr4); exact (PRS a Hi Hno Herr Hpp)|].
  split.
  { intros i Hi. rewrite K4 by lf_err_side ERF i Hi. exact (ERR3 i Hi). }
  split; [exact HRM2 | exact HCNT2].
- (* c - 1 = 0: out of the loop *)
  lazymatch goal with Hb : branch_taken _ _ _ = false |- _ => rename Hb into Hbr end.
  rewrite branch_ne_U in Hbr.
  rewrite (U_atom_off Eb 23 (Z.of_nat c) (-1) EB23) in Hbr by lia.
  rewrite U_SLit, (zcanon_id 0) in Hbr by (unfold M64; lia).
  apply Bool.negb_false_iff, Z.eqb_eq in Hbr.
  assert (Hc0 : (c - 1 =? 0)%nat = true) by (apply Nat.eqb_eq; lia).
  rewrite Hc0 in HK.
  paj_run_to_tok_x RUNTO HS HJ3 SHOK3 lf_Bspan A_lf_done.
  { lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
    apply awr_ok_x_cons_awr0; [awr_ok_tac; exact Uspb|]. apply awr_ok_x_cons_g; [|apply awr_ok_x_nil].
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]. rewrite U8b. intros a Ha. apply HLG. lia. }
  lazymatch goal with |- SRr _ _ (mkCfg ?mm _) _ => rename mm into msf end.
  lazymatch goal with Hf : frame_of _ _ (mrestrict (w_H W2) (ms_mem ms3)) (mrestrict (w_H W2) (ms_mem msf)) |- _ => rename Hf into HFr4 end.
  lazymatch goal with Hgr : mem_grows (mrestrict (w_H W2) (ms_mem ms3)) (mrestrict (w_H W2) (ms_mem msf)) |- _ => rename Hgr into HGr4 end.
  lazymatch type of HFr4 with frame_of ?Ev ?rs _ _ => let rs' := eval vm_compute in rs in change rs with rs' in HFr4 end.
  assert (K4 : forall a, 0 <= a < 2 ^ 64 -> ~ (LA <= a < LA + 16) -> aview SEGS (w_H W2) (ms_mem msf) a = aview SEGS (w_H W2) (ms_mem ms3) a).
  { intros a Ha Hno. apply (aview_kept_out _ _ (w_H W2) (ms_mem ms3) (ms_mem msf) HFr4 a Ha).
    intros (rg & Hin & Hr). cbn [In] in Hin. destruct Hin as [<- | [<- | []]];
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr; [lia | rewrite U8b in Hr; lia]. }
  pmkst HS.
  prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4. prreg HS (8%bv : bv 5) F8.
  prreg HS (9%bv : bv 5) F9. prreg HS (18%bv : bv 5) F18. prreg HS (23%bv : bv 5) F23.
  prreg HS (25%bv : bv 5) F25. prreg HS (26%bv : bv 5) F26. prreg HS (27%bv : bv 5) F27.
  prreg_raw HS (19%bv : bv 5) F19. prreg_raw HS (20%bv : bv 5) F20. prreg_raw HS (21%bv : bv 5) F21.
  pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RS0.
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RL1.
  cbn [ms_mem restrict] in RS0, RL1.
  assert (VL0 : val_mem SEGS (mrestrict (w_H W2) (ms_mem msf)) (LA + 0) (N.to_nat 8) (hl_v l)).
  { eapply (field_of_region Eb _ 8 LA); [exact RL1 | exact U8b | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
    cbn [sv_denot]. rewrite EB32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
  assert (VL8 : val_mem SEGS (mrestrict (w_H W2) (ms_mem msf)) (LA + 8) (N.to_nat 4) (Z.of_nat (c - 1))).
  { eapply (field_of_region Eb _ 8 LA); [exact RL1 | exact U8b | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
    cbn [sv_denot]. rewrite EB23, unsigned_lit_small by lia. f_equal. lia. }
  assert (VL12 : val_mem SEGS (mrestrict (w_H W2) (ms_mem msf)) (LA + 12) (N.to_nat 4) (hl_cap l)).
  { eapply (field_of_region Eb _ 8 LA); [exact RL1 | exact U8b | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
    cbn [sv_denot]. rewrite EB33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
  rewrite Z.add_0_r in VL0.
  assert (HAWR : awr W2 (ms_mem msf) LA 16).
  { intros i Hi. destruct RL1 as (_ & _ & RLw & _). cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in RLw.
    rewrite U8b in RLw. exact (RLw i Hi). }
  assert (HVEC' : 0 < hl_cap l -> In (hl_v l, AREC * hl_cap l) (ablocks B ly2 S2) /\
    garr8 SEGS (arm W2 (ms_mem msf)) (hl_v l) (bzs (concat (map text_rec (hl_recs l)) ++ hl_junk l))).
  { intros _. split; [exact Hvin2|]. unfold arm in Hvg |- *.
    apply (lf_garr8_kept (w_H Wc) (w_H W2) memc (ms_mem msf)); [|exact Hvg].
    intros j Hj. rewrite Hvlen in Hj. rewrite K4 by (unfold alloc_ceiling in *; lia). apply VEC. lia. }
  eapply (HK W2 ly2 S2 Hp2 (ms_regs msf) (ms_mem msf) _ (kk + 1)).
  unfold lf_inv_x.
  split; [exact HJ3|].
  split.
  { unfold lf_regs.
    split; [rewrite F2, OLDb, OLDa by lia; rewrite E2; exact R2|].
    split; [rewrite F3, OLDb, OLDa by lia; exact E3|].
    split; [rewrite F4, OLDb, OLDa by lia; exact E4|].
    split; [rewrite F8, OLDb, OLDa by lia; exact E8|].
    split; [rewrite F9, U8b; reflexivity|].
    split; [rewrite F18, OLDb, OLDa by lia; exact E18|].
    split; [rewrite F19; exact D19|].
    split; [rewrite F20; exact D20|].
    split; [rewrite F21; exact D21|].
    split; [rewrite F23, EB23, unsigned_lit_small by lia; f_equal; lia|].
    split; [rewrite F25, OLDb, OLDa by lia; exact E25|].
    split; [rewrite F26, OLDb, OLDa by lia; exact E26|].
    rewrite F27, OLDb, OLDa by lia; exact E27. }
  split.
  { intros i Hi. unfold arm.
    pose proof (bv_unsigned_in_range 64 (getr regs0 (Z_to_bv 5 (nth i lf_saved 0)))) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
    eapply (slot_of_region Eb _ (spZ regs0 - 80) _ 0 80 0 0 (8 * Z.of_nat i) (SOff (34 + i) 0)).
    - exact RS0.
    - exact Uspb.
    - clear - Hi. do 10 (destruct i as [|i]; [cbn [In]; repeat first [left; reflexivity | right] |]). lia.
    - cbn [sv_denot]. rewrite OLDb, OLDa by lia. rewrite (ESV i Hi), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    - exact Hr. }
  split; [exact VL0|]. split; [exact VL8|]. split; [exact VL12|]. split; [exact HAWR|]. split; [exact HVEC'|].
  split; [exact HTX2|]. split; [exact HPERM2|]. split; [exact HFRS2|]. split; [exact HML2'|].
  split; [intros a Hi Hno Herr Hpp; apply (lf_apresent_grows _ _ _ a HGr4); exact (PRS a Hi Hno Herr Hpp)|].
  split.
  { intros i Hi. rewrite K4 by lf_err_side ERF i Hi. exact (ERR3 i Hi). }
  split; [exact HRM2 | exact HCNT2].
Qed.
(* ---- after the loop (0x86164): free(v) (free(NULL) when the list never had a vector), v = 0, cap = 0, the
   epilogue and the ret ---- *)
Lemma lf_exit_x : forall W ly S Hp regs0 mem0 md0 ch LA (l : hlist) lines kr Wc lyc Sc Hpc regs memc mdc kk,
lf_ctx_x W ly S Hp regs0 mem0 md0 ch LA l lines ->
ajournal_gx_x SEGS B PST ARx G 0 [] LF_STK (spZ regs0) (blk_FP (list_blks l)) ly S Hp W mem0 md0 [] lyc Sc Hpc Wc memc mdc kk ->
lf_regsT regs regs0 LA -> lf_frame Wc memc (spZ regs0) regs0 ->
val_mem SEGS (arm Wc memc) LA 8 (hl_v l) -> val_mem SEGS (arm Wc memc) (LA + 8) 4 0 ->
val_mem SEGS (arm Wc memc) (LA + 12) 4 (hl_cap l) -> awr Wc memc LA 16 ->
(0 < hl_cap l -> In (hl_v l, AREC * hl_cap l) (ablocks B lyc Sc)) ->
(forall rest, Permutation (ablocks B ly S) (list_blks l ++ rest) -> Permutation (ablocks B lyc Sc) (lf_blks l 0 ++ rest)) ->
frames Sc = frames S -> mo_le MT S Sc (hl_n l * mo_free MT) -> apres_kept B W mem0 Wc memc ->
(forall i, 0 <= i < 4 -> aview SEGS (w_H Wc) memc (as_errno B + i) = aview SEGS (w_H W) mem0 (as_errno B + i)) ->
rp_RM RP Sc (1 + kr) -> cnt_ok RP (ablocks B lyc Sc) ->
SRr SEGS Wc (mkCfg (mkst regs (Z_to_bv 64 (BASE + A_lf_done)) memc (seg_rom SEGS)) mdc)
  (lf_post_x B PST ARx MT RP G regs0 ly S Hp W mem0 md0 LA l lines kr).
Proof.
intros W ly S Hp regs0 mem0 md0 ch LA l lines kr Wc lyc Sc Hpc regs memc mdc kk HCTX HJ HR Hfr Mv Mn Mc Hw HVEC HPERM HFRS HMLE HAPK HERR HRM HCNT.
destruct HCTX as (HPRE & HL & HLG & HZS & HROM & HMO).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof (lf_LA_range LA HLG) as (HLA1 & HLA2 & _ & _ & HLAe).
pose proof (lf_errno_facts (spZ regs0) LA ltac:(clear - Hceil Hslo; lia) HLG) as ERF.
pose proof HL as (_ & _ & _ & _ & (Hn0 & Hcap) & Hvc & Hnd & Hnv & HFA).
pose proof (ajournal_gx_AR_x SEGS B PST ARx G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARc.
assert (Hsp0 : lf_sp0 (spZ regs0)) by (split; [exact Hal16 | clear - Hceil Hslo Hshi H47; unfold LF_STK, ASTACK in *; lia]).
pose proof Hsp0 as (Hsp0a & Hsp0b & Hsp0c).
assert (Hv64 : 0 <= hl_v l < 2 ^ 48).
{ destruct Hvc as [[_ ->] | (Hcp & Hin & _)]; [lia|].
  destruct (alx_blocks _ _ _ LAWS ly S Hp W mem0 md0 _ _ HAR0 Hin) as (_ & H4096 & Hce & _).
  unfold req_size, AREC in Hce. destruct (Z.eqb_spec (16 * hl_cap l) 0); lia. }
destruct (lf_head_exit_x Wc lyc Sc Hpc memc mdc regs regs0 LA (hl_v l) (hl_cap l) HARc HR Hsp0 Hfr HLA1 HLA2 HZS Mv Mn Mc Hw
  ltac:(lia) ltac:(lia)) as [HS SHOK].
remember (Eimg (Ereg regs (lf_xl (hl_v l) (hl_cap l) 0 0 regs0))) as E eqn:HE in HS.
rewrite <- HE in SHOK.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
destruct HR as (R2 & R3 & R4 & R8 & R18 & R20 & R25 & R26 & R27).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs0 - 80) by (rewrite E2, R2; apply unsigned_lit_small; lia).
assert (E3 : ew E 3 = getr regs0 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 3 3%bv eq_refl); exact R3).
assert (E4 : ew E 4 = getr regs0 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 4 4%bv eq_refl); exact R4).
assert (E8 : ew E 8 = Z_to_bv 64 LA) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 8 8%bv eq_refl); exact R8).
assert (E18 : ew E 18 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact R18).
assert (E25 : ew E 25 = getr regs0 25) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact R25).
assert (E26 : ew E 26 = getr regs0 26) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact R26).
assert (E27 : ew E 27 = getr regs0 27) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact R27).
assert (E32 : ew E 32 = Z_to_bv 64 (hl_v l)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (ESV : forall i, (i < 10)%nat -> ew E (34 + i) = getr regs0 (Z_to_bv 5 (nth i lf_saved 0)))
by (intros i Hi; subst E; exact (lf_ew_saved regs regs0 _ _ _ _ i Hi)).
assert (U8 : bv_unsigned (ew E 8) = LA) by (rewrite E8; apply unsigned_lit_small; lia).
assert (HMOf : mo_ok MT Sc (mo_free MT)).
{ pose proof (mo_free_nonneg MT MLAW) as Hf.
  apply (mok_station MT S Sc (lf_cost MT l) (hl_n l * mo_free MT) (mo_free MT) MLAW HMO HMLE Hf).
  unfold lf_cost. nia. }
(* 0x86164 .. the jal to free *)
paj_run_tok_x RUN HS HJ SHOK lf_Bspan.
{ apply awr_ok_x_cons_awr0; [awr_ok_tac; exact Usp|]. apply awr_ok_x_cons_g; [|apply awr_ok_x_nil].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi lf_lregX lf_lreg base_val]. rewrite U8. intros a Ha. apply HLG. lia. }
lazymatch goal with |- SRr _ _ (mkCfg ?mm _) _ => rename mm into ms end.
lazymatch goal with Hgr : mem_grows (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) (ms_mem ms)) |- _ =>
  assert (PR1 : forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) (ms_mem ms) a)
  by (intros a Hpp; exact (lf_apresent_grows (w_H Wc) memc (ms_mem ms) a Hgr Hpp)) end.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (LA <= a < LA + 16) -> aview SEGS (w_H Wc) (ms_mem ms) a = aview SEGS (w_H Wc) memc a).
{ intros a Ha Hno. lazymatch goal with Hf : frame_of _ _ (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) (ms_mem ms)) |- _ =>
    apply (aview_kept_out _ _ (w_H Wc) memc (ms_mem ms) Hf a Ha) end.
  intros (rg & Hin & Hr). cbn [ss_mem ss_lfX In] in Hin. destruct Hin as [<- | [<- | []]];
  cbn [lf_stackL lf_lregX lf_lreg YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr;
  [lia | rewrite U8 in Hr; lia]. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.
destruct HJ as (HSTK & HXO & (memS & HJi & Hag) & Hout). rewrite !Z.add_0_r in HJi.
pose proof (proj1 HJi) as HARm.
assert (Usp2 : spZ (ms_regs ms) = spZ regs0 + -80) by (unfold spZ at 1; rewrite Q2, Usp; lia).
assert (R10s : getr (ms_regs ms) 10 = w64 (hl_v l)) by (rewrite Q10; exact E32).
assert (HGP : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite Q3, E3; exact Hgp).
assert (HTP : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite Q4, E4; exact Htp).
assert (HS0 : s0Z (ms_regs ms) = LA) by (unfold s0Z; rewrite Q8; exact U8).
assert (HCH : chain_pre lyc (aview SEGS (w_H Wc) (ms_mem ms)) (ms_regs ms) []).
{ unfold chain_pre. split; [unfold raZ; rewrite Q1; rewrite unsigned_lit_small by lia; lia|].
  destruct (frame0_ok lyc (ms_regs ms)); [|reflexivity].
  replace (bad_next (spZ (ms_regs ms)) (ly_top lyc) (s0Z (ms_regs ms))) with true; [reflexivity|].
  symmetry. unfold bad_next. rewrite HS0, Usp2. apply orb_true_iff. left. apply orb_true_iff. left. apply Z.leb_le. lia. }
(* the free's caller context: the chain is [] (s0 = LA, an image address), the trace the singleton [list_free + 0xf8] *)
assert (HCTXX : In (raZ (ms_regs ms) :: spine []) CTX).
{ cbn [spine map]. replace (raZ (ms_regs ms)) with (BASE + AF_fr_list_free + 0xf8); [exact HCTX_lf_exit|].
  unfold raZ. rewrite Q1, unsigned_lit_small by lia. first [lia | unfold AF_fr_list_free in *; lia]. }
rewrite HBfree.
(* free(v), or free(NULL) when cap = 0: the same bookkeeping either way *)
eapply SRr_bind with (R := fun W4 c4 => exists ly4 S4 Hp4 regs4 mem4 md4,
  c4 = mkCfg (mkst regs4 (getr (ms_regs ms) 1) mem4 (seg_rom SEGS)) md4 /\
  ajournal_x SEGS B PST ARx LF_STK (spZ regs0) (blk_FP (list_blks l)) ly S Hp W memS md0 [] ly4 S4 Hp4 W4 mem4 md4 (kk + 1) /\
  aregs_preserved (ms_regs ms) regs4 /\
  (forall rest, Permutation (ablocks B lyc Sc) (lf_blks l 0 ++ rest) -> Permutation (ablocks B ly4 S4) rest) /\
  frames S4 = frames Sc /\
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs0 + -80 - ASTACK <= a < spZ regs0 + -80) ->
   aview SEGS (w_H W4) mem4 a = aview SEGS (w_H Wc) (ms_mem ms) a) /\
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
   aview SEGS (w_H W4) mem4 a = aview SEGS (w_H Wc) (ms_mem ms) a) /\
  mo_le MT Sc S4 (mo_free MT) /\ rp_RM RP S4 kr /\
  (forall i, 0 <= i < 4 -> aview SEGS (w_H W4) mem4 (as_errno B + i) = aview SEGS (w_H Wc) (ms_mem ms) (as_errno B + i)) /\
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
   apresent (w_H Wc) (ms_mem ms) a -> apresent (w_H W4) mem4 a)).
{ destruct (Z.eq_dec (hl_cap l) 0) as [Hc0 | Hc0].
  - assert (Hv0 : hl_v l = 0) by (destruct Hvc as [[_ H] | (Hcp & _)]; [exact H | lia]).
    eapply SRr_mono.
    { exact (AFREEN Wc (ms_regs ms) (ms_mem ms) LF_STK (spZ regs0) (blk_FP (list_blks l)) ly S Hp W memS md0 [] lyc Sc Hpc _ _
        (-80) (getr (ms_regs ms) 1) [] kr HJi ltac:(rewrite R10s, Hv0; reflexivity) Usp2 eq_refl ltac:(lia)
        ltac:(unfold LF_STK, ASTACK; lia)
        (aj_stack_room_x SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (-80) (ms_regs ms) HJi Usp2 ltac:(unfold LF_STK, ASTACK; lia))
        HGP HTP eq_refl ltac:(rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]) HCH HCTXX HRM HCNT HMOf). }
    cbv beta. intros W4 c4 _ (ly4 & S4 & Hp4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & HPm & HFr4 & HK4 & HM4 & HRM4 & HE4 & HPr4).
    exists ly4, S4, Hp4, regs4, mem4, md4. split; [reflexivity|]. split; [exact HJ4|]. split; [exact HP4|].
    split.
    { intros rest Hpp. unfold lf_blks in Hpp. rewrite (proj2 (Z.eqb_eq _ _) Hc0) in Hpp. cbn [firstn map app] in Hpp.
      exact (Permutation_trans HPm Hpp). }
    split; [exact HFr4|].
    split; [exact (proj1 HK4)|].
    split; [exact (proj1 (proj2 (proj2 HK4)))|].
    split; [exact HM4|]. split; [exact HRM4|]. split; [exact HE4|].
    intros a Hi Ho He Hpp. pose proof (proj1 HJ4) as HAR4.
    apply (HPr4 a Hi); [intros Hao; apply Ho; exact (proj1 (alx_owned_image _ _ _ LAWS _ _ _ _ _ _ a HARm Hi) Hao)
      | intros Hao; apply Ho; exact (proj1 (alx_owned_image _ _ _ LAWS _ _ _ _ _ _ a HAR4 Hi) Hao) | exact He | exact Hpp].
  - assert (Hcp : 0 < hl_cap l) by lia.
    pose proof (HVEC Hcp) as Hvin.
    eapply SRr_mono.
    { exact (AFREE Wc (ms_regs ms) (ms_mem ms) LF_STK (spZ regs0) (blk_FP (list_blks l)) ly S Hp W memS md0 [] lyc Sc Hpc _ _
        (hl_v l) (AREC * hl_cap l) (-80) (getr (ms_regs ms) 1) [] kr HJi Hvin R10s Usp2 eq_refl ltac:(lia)
        ltac:(unfold LF_STK, ASTACK; lia)
        (aj_stack_room_x SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (-80) (ms_regs ms) HJi Usp2 ltac:(unfold LF_STK, ASTACK; lia))
        HGP HTP eq_refl ltac:(rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]) HCH HCTXX HRM HCNT
        ltac:(intros _ i Hi; apply (inFP_ablocks_fp (list_blks l) (hl_v l) (AREC * hl_cap l) i);
              [unfold list_blks; rewrite (proj2 (Z.eqb_neq _ _) Hc0); apply in_or_app; left; left; reflexivity | exact Hi]) HMOf). }
    cbv beta. intros W4 c4 _ (ly4 & S4 & Hp4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & (l1 & l2 & Eb1 & Eb2) & HFr4 & HK4 & HM4 & HRM4 & HE4 & HPr4).
    exists ly4, S4, Hp4, regs4, mem4, md4. split; [reflexivity|]. split; [exact HJ4|]. split; [exact HP4|].
    split.
    { intros rest Hpp. rewrite Eb2. rewrite Eb1 in Hpp. unfold lf_blks in Hpp. rewrite (proj2 (Z.eqb_neq _ _) Hc0) in Hpp.
      cbn [firstn map app] in Hpp. apply Permutation_sym in Hpp. apply Permutation_cons_app_inv in Hpp. exact (Permutation_sym Hpp). }
    split; [exact HFr4|].
    split; [exact (proj1 HK4)|].
    split; [exact (proj1 (proj2 (proj2 HK4)))|].
    split; [exact HM4|]. split; [exact HRM4|]. split; [exact HE4|].
    intros a Hi Ho He Hpp. pose proof (proj1 HJ4) as HAR4.
    apply (HPr4 a Hi); [intros Hao; apply Ho; exact (proj1 (alx_owned_image _ _ _ LAWS _ _ _ _ _ _ a HARm Hi) Hao)
      | intros Hao; apply Ho; exact (proj1 (alx_owned_image _ _ _ LAWS _ _ _ _ _ _ a HAR4 Hi) Hao) | exact He | | exact Hpp].
    intros Hb. exact (blk_img_x SEGS B ARx LAWS lyc Sc Hpc Wc (ms_mem ms) _ _ _ a HARm Hvin Hb Hi). }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & Hp4 & regs4 & mem4 & md4 & -> & HJi4 & HP4 & HPM4 & HFR4 & KS4 & KI4 & HML4 & HRM4 & HER4 & HPR4).
rewrite Q1.
pose proof (proj1 HJi4) as HAR4.
assert (HJ4 : ajournal_gx_x SEGS B PST ARx G 0 [] LF_STK (spZ regs0) (blk_FP (list_blks l)) ly S Hp W mem0 md0 [] ly4 S4 Hp4 W4 mem4 md4 (kk + 1)).
{ apply (ajournal_gx_pack_x SEGS B PST ARx G 0 [] LF_STK (spZ regs0) _ ly S Hp W mem0 md0 [] ly4 S4 Hp4 W4 mem4 md4 (kk + 1) memS HSTK HXO);
  [rewrite !Z.add_0_r; exact HJi4 | exact Hag | apply out_none]. }
(* ---- keep the frame and the list struct across the call ---- *)
assert (HLAimg : forall a, LA <= a < LA + 16 ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4))
by (intros a Ha; exact (conj (proj1 (HG a (HLG a Ha))) (conj (proj1 (proj2 (HG a (HLG a Ha)))) (proj1 (HGR a (HLG a Ha)))))).
jafter_call_keep_pi HS 46%nat regs4 (mrestrict (w_H W4) mem4) HP4 [0; 1]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - apply (lf_region_kept2 E Wc W4 (ms_mem ms) mem4 2 (spZ regs0 - 80)); [exact Usp | | intros a Ha; exfalso; lia].
    intros a Ha. apply KS4; [lia | lia].
  - apply (lf_region_kept2 E Wc W4 (ms_mem ms) mem4 8 LA); [exact U8 | |].
    + intros a Ha. destruct (HLAimg a ltac:(lia)) as (Hi & Ho & He). exact (KI4 a Hi Ho He).
    + intros a Ha. destruct (HLAimg a ltac:(lia)) as (Hi & Ho & He).
      apply (lf_writable_img Wc W4 (ms_mem ms) mem4 a Hi). exact (HPR4 a Hi Ho He). }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 46 (map (getr regs4) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 46)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
clear HEa.
assert (SHOK2 : sh_ok SEGS lf_BxL lf_SHT Ea (mrestrict (w_H W4) mem4)).
{ unfold sh_ok, lf_SHT. constructor; [|constructor].
  apply (lf_shent8_x Ea ly4 S4 Hp4 W4 mem4 md4 LA HAR4 HZS); [rewrite OLDa by lia; exact E8 | rewrite OLDa by lia; exact E18 | exact HLA1 | exact HLA2]. }
assert (Uspa : bv_unsigned (ew Ea 2) = spZ regs0 - 80) by (rewrite OLDa by lia; exact Usp).
assert (U8a : bv_unsigned (ew Ea 8) = LA) by (rewrite OLDa by lia; exact U8).
(* 0x86178 .. the ret: v = 0, cap = 0, the epilogue *)
paj_run_tok_x RUN HS HJ4 SHOK2 lf_Bspan.
{ apply awr_ok_x_cons_awr0; [awr_ok_tac; exact Uspa|]. apply awr_ok_x_cons_g; [|apply awr_ok_x_nil].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]. rewrite U8a. intros a Ha. apply HLG. lia. }
lazymatch goal with |- SRr _ _ (mkCfg ?mm _) _ => rename mm into msf end.
lazymatch goal with Hgr : mem_grows (mrestrict (w_H W4) mem4) (mrestrict (w_H W4) (ms_mem msf)) |- _ => rename Hgr into HGrf end.
lazymatch goal with Hf : frame_of _ _ (mrestrict (w_H W4) mem4) (mrestrict (w_H W4) (ms_mem msf)) |- _ => rename Hf into HFrf end.
assert (Kf : forall a, 0 <= a < 2 ^ 64 -> ~ (LA <= a < LA + 16) -> aview SEGS (w_H W4) (ms_mem msf) a = aview SEGS (w_H W4) mem4 a).
{ intros a Ha Hno. apply (aview_kept_out _ _ (w_H W4) mem4 (ms_mem msf) HFrf a Ha).
  intros (rg & Hin & Hr). cbn [In] in Hin. destruct Hin as [<- | [<- | []]];
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr; [lia | rewrite U8a in Hr; lia]. }
prreg HS (1%bv : bv 5) F1. prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4.
prreg HS (8%bv : bv 5) F8. prreg HS (9%bv : bv 5) F9. prreg HS (18%bv : bv 5) F18. prreg HS (19%bv : bv 5) F19.
prreg HS (20%bv : bv 5) F20. prreg HS (21%bv : bv 5) F21. prreg HS (22%bv : bv 5) F22. prreg HS (23%bv : bv 5) F23.
prreg HS (24%bv : bv 5) F24. prreg HS (25%bv : bv 5) F25. prreg HS (26%bv : bv 5) F26. prreg HS (27%bv : bv 5) F27.
assert (HPF : aregs_preserved regs0 (ms_regs msf)).
{ apply aregs_preserved_eqs.
  - rewrite F2, Uspa. replace (spZ regs0 - 80 + 80) with (spZ regs0) by lia. unfold spZ. apply Z_to_bv_bv_unsigned.
  - rewrite F3, OLDa by lia. exact E3.
  - rewrite F4, OLDa by lia. exact E4.
  - rewrite F8, OLDa by lia. exact (ESV 8%nat ltac:(lia)).
  - rewrite F9, OLDa by lia. exact (ESV 7%nat ltac:(lia)).
  - rewrite F18, OLDa by lia. exact (ESV 6%nat ltac:(lia)).
  - rewrite F19, OLDa by lia. exact (ESV 5%nat ltac:(lia)).
  - rewrite F20, OLDa by lia. exact (ESV 4%nat ltac:(lia)).
  - rewrite F21, OLDa by lia. exact (ESV 3%nat ltac:(lia)).
  - rewrite F22, OLDa by lia. exact (ESV 2%nat ltac:(lia)).
  - rewrite F23, OLDa by lia. exact (ESV 1%nat ltac:(lia)).
  - rewrite F24, OLDa by lia. exact (ESV 0%nat ltac:(lia)).
  - rewrite F25, OLDa by lia. exact E25.
  - rewrite F26, OLDa by lia. exact E26.
  - rewrite F27, OLDa by lia. exact E27. }
assert (ER1 : ew E 43 = getr regs0 1) by exact (ESV 9%nat ltac:(lia)).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ => set (Ef := Ev) in HS end.
assert (UF : forall m, (m < 512)%nat -> ew Ef m = ew Ea m) by (intros m Hm; subst Ef; rewrite ?ew_ewset_other by lia; reflexivity).
assert (U8f : bv_unsigned (ew Ef 8) = LA) by (rewrite UF by lia; exact U8a).
pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RL1. cbn [ms_mem restrict] in RL1.
assert (VL0 : val_mem SEGS (mrestrict (w_H W4) (ms_mem msf)) (LA + 0) (N.to_nat 8) 0).
{ eapply (field_of_region Ef _ 8 LA); [exact RL1 | exact U8f | cbn [In]; repeat first [left; reflexivity | right] | reflexivity | zside | zside]. }
assert (VL8 : val_mem SEGS (mrestrict (w_H W4) (ms_mem msf)) (LA + 8) (N.to_nat 4) 0).
{ eapply (field_of_region Ef _ 8 LA); [exact RL1 | exact U8f | cbn [In]; repeat first [left; reflexivity | right] | reflexivity | zside | zside]. }
assert (VL12 : val_mem SEGS (mrestrict (w_H W4) (ms_mem msf)) (LA + 12) (N.to_nat 4) 0).
{ eapply (field_of_region Ef _ 8 LA); [exact RL1 | exact U8f | cbn [In]; repeat first [left; reflexivity | right] | reflexivity | zside | zside]. }
rewrite Z.add_0_r in VL0.
assert (HAWR : awr W4 (ms_mem msf) LA 16).
{ intros i Hi. destruct RL1 as (_ & _ & RLw & _). cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in RLw.
  rewrite U8f in RLw. exact (RLw i Hi). }
eapply (RET W4 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros matf. unfold lf_post_x.
exists ly4, S4, Hp4, (ms_regs msf), (ms_mem msf). eexists. exists (kk + 1).
split; [rewrite F1, OLDa by lia; rewrite ER1, Hra; reflexivity|].
split; [apply (ajournal_gx_materialize_x SEGS B PST ARx LAWS Hsegs); exact HJ4|].
split; [exact HPF|].
split.
{ unfold alist_at, empty_list, hl_n. cbn [hl_v hl_cap hl_recs hl_junk length Z.of_nat].
  split; [exact VL0|]. split; [exact VL8|]. split; [exact VL12|]. split; [exact HAWR|].
  split; [lia|]. split; [left; split; reflexivity|]. split; [constructor|]. split; [intros []|]. constructor. }
split; [intros rest Hpp; exact (HPM4 rest (HPERM rest Hpp))|].
split.
{ intros a Hi Hno Herr Hpp. apply (lf_apresent_grows _ _ _ a HGrf). apply (HPR4 a Hi Hno Herr). apply PR1.
  exact (HAPK a Hi Hno Herr Hpp). }
split.
{ intros i Hi. rewrite Kf by lf_err_side ERF i Hi. rewrite (HER4 i Hi). rewrite K1 by lf_err_side ERF i Hi. exact (HERR i Hi). }
split; [rewrite HFR4; exact HFRS|].
split; [|exact HRM4].
replace (lf_cost MT l) with (hl_n l * mo_free MT + mo_free MT) by (unfold lf_cost; ring).
exact (mle_station MT S Sc S4 _ _ MLAW HMLE HML4).
Qed.
Lemma lf_exit_inv_x : forall W ly S Hp regs0 mem0 md0 ch LA (l : hlist) lines kr Wc lyc Sc Hpc regs memc mdc kk,
lf_ctx_x W ly S Hp regs0 mem0 md0 ch LA l lines -> lf_inv_x W ly S Hp regs0 mem0 md0 LA l 0 kr Wc lyc Sc Hpc regs memc mdc kk ->
SRr SEGS Wc (mkCfg (mkst regs (Z_to_bv 64 (BASE + A_lf_done)) memc (seg_rom SEGS)) mdc)
  (lf_post_x B PST ARx MT RP G regs0 ly S Hp W mem0 md0 LA l lines kr).
Proof.
intros W ly S Hp regs0 mem0 md0 ch LA l lines kr Wc lyc Sc Hpc regs memc mdc kk HCTX
  (HJ & HR & Hfr & Mv & Mn & Mc & Hw & HVEC & _ & HPERM & HFRS & HMLE & HAPK & HERR & HRM & HCNT).
destruct HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R21 & R23 & R25 & R26 & R27).
apply (lf_exit_x W ly S Hp regs0 mem0 md0 ch LA l lines kr Wc lyc Sc Hpc regs memc mdc kk HCTX HJ).
- unfold lf_regsT. repeat (split; [assumption|]). assumption.
- exact Hfr.
- exact Mv.
- exact Mn.
- exact Mc.
- exact Hw.
- intros Hc. exact (proj1 (HVEC Hc)).
- exact HPERM.
- exact HFRS.
- replace (hl_n l * mo_free MT) with ((hl_n l - Z.of_nat 0) * mo_free MT) by (cbn [Z.of_nat]; ring). exact HMLE.
- exact HAPK.
- exact HERR.
- exact HRM.
- exact HCNT.
Qed.

Theorem pb_list_free_x : lf_spec_x B PST ARx MT RP G A_list_freeP.
Proof.
intros W ly S Hp regs mem md ch LA l lines HPRE H10 HAL8 HL HLG HZS HROM HMO kr HRM0 HCNT0.
assert (HCTX : lf_ctx_x W ly S Hp regs mem md ch LA l lines) by (exact (conj HPRE (conj HL (conj HLG (conj HZS (conj HROM HMO)))))).
(* the loop, by induction on the texts left *)
assert (IND : forall c Wc lyc Sc Hpc regsc memc mdc kc, (c <= length (hl_recs l))%nat ->
  lf_inv_x W ly S Hp regs mem md LA l c kr Wc lyc Sc Hpc regsc memc mdc kc ->
  SRr SEGS Wc (mkCfg (mkst regsc (Z_to_bv 64 (BASE + if (c =? 0)%nat then A_lf_done else A_lf_loop)) memc (seg_rom SEGS)) mdc)
    (lf_post_x B PST ARx MT RP G regs ly S Hp W mem md LA l lines kr)).
{ induction c as [|c IH]; intros Wc lyc Sc Hpc regsc memc mdc kc Hcl HI; cbn [Nat.eqb].
  - exact (lf_exit_inv_x W ly S Hp regs mem md ch LA l lines kr Wc lyc Sc Hpc regsc memc mdc kc HCTX HI).
  - apply (lf_iter_x (Datatypes.S c) W ly S Hp regs mem md ch LA l lines kr Wc lyc Sc Hpc regsc memc mdc kc HCTX ltac:(lia) HI).
    intros Wc' lyc' Sc' Hpc' regs' memc' mdc' kk' HI'.
    replace (Datatypes.S c - 1)%nat with c in * by lia. exact (IH Wc' lyc' Sc' Hpc' regs' memc' mdc' kk' ltac:(lia) HI'). }
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct (lf_entry_x W ly S Hp regs mem md ch LA l lines HPRE H10 HL HLG HZS) as [HS SHOK].
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof HL as (Mv & Mn & Mc & Hw & (Hn0 & Hcap) & Hvc & Hnd & Hnv & HFA).
pose proof (ajournal_gx_init_x SEGS B PST ARx G 0 [] LF_STK (blk_FP (list_blks l)) ly S Hp W regs mem md ch HPRE
  ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(intros a Ha; lia)) as HJ.
remember (Eimg (Ereg regs (lf_extra l))) as E eqn:HE in HS.
rewrite <- HE in SHOK.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E25 : ew E 25 = getr regs 25) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 25 25%bv eq_refl)).
assert (E26 : ew E 26 = getr regs 26) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 26 26%bv eq_refl)).
assert (E27 : ew E 27 = getr regs 27) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 27 27%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 LA) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 (hl_v l)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (hl_n l)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (hl_cap l)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (ERS : forall i, (i < 10)%nat -> ew E (Z.to_nat (nth i lf_saved 0)) = getr regs (Z_to_bv 5 (nth i lf_saved 0)))
by (intros i Hi; subst E; exact (lf_ew_regs regs _ i Hi)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
pose proof (lf_LA_range LA HLG) as (HLA1 & HLA2 & _).
pose proof (lf_errno_facts (spZ regs) LA ltac:(clear - Hceil Hslo; lia) HLG) as ERF.
assert (U10 : bv_unsigned (ew E 10) = LA) by (rewrite E10; apply unsigned_lit_small; lia).
assert (HnZ : 0 <= hl_n l) by (unfold hl_n; lia).
assert (Hv64 : 0 <= hl_v l < 2 ^ 48).
{ destruct Hvc as [[_ ->] | (Hcp & Hin & _)]; [lia|].
  destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hin) as (_ & H4096 & Hce & _).
  unfold req_size, AREC in Hce. destruct (Z.eqb_spec (16 * hl_cap l) 0); lia. }
destruct (lf_den_regs E LA E10 E35 ltac:(lia)) as (D9 & D19 & D20 & D21).
unfold cfg_at. change (w64 A_list_freeP) with (Z_to_bv 64 A_list_freeP).
unfold A_list_freeP, A_list_free.
(* the prologue, to the test of n *)
paj_run_tok_x RUN HS HJ SHOK lf_Bspan.
{ apply awr_ok_x_cons_awr0; [awr_ok_tac; exact Usp|]. apply awr_ok_x_cons_awr0; [awr_ok_tac|].
  apply awr_ok_x_cons_awr0; [awr_ok_tac|]. apply awr_ok_x_cons_g; [|apply awr_ok_x_nil].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi lf_lreg base_val]. rewrite U10.
  intros a Ha. apply HLG. lia. }
lazymatch goal with |- SRr _ _ (mkCfg ?mm _) _ => rename mm into ms0 end.
lazymatch goal with Hf : frame_of _ _ (mrestrict (w_H W) mem) (mrestrict (w_H W) (ms_mem ms0)) |- _ => rename Hf into HFr0 end.
lazymatch goal with Hgr : mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) (ms_mem ms0)) |- _ => rename Hgr into HGr0 end.
assert (K0 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 80 <= a < spZ regs) -> ~ (LA <= a < LA + 16) ->
  aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a).
{ intros a Ha H1 H2. apply (aview_kept_out _ _ (w_H W) mem (ms_mem ms0) HFr0 a Ha).
  intros (rg & Hin & Hr). cbn [ss_mem ss_lf0 lf_regions0 In] in Hin. destruct Hin as [<- | [<- | [<- | [<- | []]]]];
  cbn [stack_region got_regionP bcell_regionP lf_lreg LF_FRAME YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr;
  [rewrite Usp in Hr; unfold LF_FRAME in Hr; lia | lia | lia | rewrite U10 in Hr; lia]. }
psrr_branch_tok RUN BR HS SHOK lf_Bspan.
- (* n = 0: straight to the exit *)
  lazymatch goal with Hb : branch_taken _ _ _ = true |- _ => rename Hb into Hbr end.
  rewrite branch_eq_U in Hbr. rewrite (U_atom E 33 (hl_n l) E33) in Hbr by lia.
  rewrite U_SLit, (zcanon_id 0) in Hbr by (unfold M64; lia).
  apply Z.eqb_eq in Hbr.
  assert (Hrn : hl_recs l = []) by (unfold hl_n in Hbr; destruct (hl_recs l); [reflexivity | cbn [length] in Hbr; lia]).
  paj_run_to_tok_x RUNTO HS HJ SHOK lf_Bspan A_lf_done.
  { lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
    apply awr_ok_x_cons_awr0; [awr_ok_tac; exact Usp|]. apply awr_ok_x_cons_awr0; [awr_ok_tac|].
    apply awr_ok_x_cons_awr0; [awr_ok_tac|]. apply awr_ok_x_cons_g; [|apply awr_ok_x_nil].
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]. rewrite U10. intros a Ha. apply HLG. lia. }
  lazymatch goal with |- SRr _ _ (mkCfg ?mm _) _ => rename mm into msf end.
  lazymatch goal with Hgr : mem_grows (mrestrict (w_H W) (ms_mem ms0)) (mrestrict (w_H W) (ms_mem msf)) |- _ => rename Hgr into HGrf end.
  lazymatch goal with Hf : frame_of _ _ (mrestrict (w_H W) (ms_mem ms0)) (mrestrict (w_H W) (ms_mem msf)) |- _ => rename Hf into HFrf end.
  lazymatch type of HFrf with frame_of ?Ev ?rs _ _ => let rs' := eval vm_compute in rs in change rs with rs' in HFrf end.
  assert (K5 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 80 <= a < spZ regs) -> ~ (LA <= a < LA + 16) ->
    aview SEGS (w_H W) (ms_mem msf) a = aview SEGS (w_H W) (ms_mem ms0) a).
  { intros a Ha H1 H2. apply (aview_kept_out _ _ (w_H W) (ms_mem ms0) (ms_mem msf) HFrf a Ha).
    intros (rg & Hin & Hr). cbn [In] in Hin. destruct Hin as [<- | [<- | [<- | [<- | []]]]];
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr;
    [rewrite Usp in Hr; lia | lia | lia | rewrite U10 in Hr; lia]. }
  pmkst HS.
  prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4. prreg HS (8%bv : bv 5) F8.
  prreg HS (18%bv : bv 5) F18. prreg HS (25%bv : bv 5) F25. prreg HS (26%bv : bv 5) F26. prreg HS (27%bv : bv 5) F27.
  prreg_raw HS (20%bv : bv 5) F20.
  pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RS0.
  pose proof (st_ok_pi_region_nth _ _ _ 3 _ HS eq_refl) as RL3.
  cbn [ms_mem restrict] in RS0, RL3.
  assert (FRM0 : lf_frame W (ms_mem msf) (spZ regs) regs).
  { intros i Hi. unfold arm.
    pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 (nth i lf_saved 0)))) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
    replace (spZ regs - 80 + 8 * Z.of_nat i) with (spZ regs + (-80 + 8 * Z.of_nat i)) by ring.
    eapply (slot_of_region E _ (spZ regs) _ (-80) 0 (-80) 0 (-80 + 8 * Z.of_nat i) (SOff (Z.to_nat (nth i lf_saved 0)) 0)).
    - exact RS0.
    - exact Usp.
    - clear - Hi. do 10 (destruct i as [|i]; [cbn [In]; repeat first [left; reflexivity | right] |]). lia.
    - cbn [sv_denot]. rewrite (ERS i Hi), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    - exact Hr. }
  assert (VL0 : val_mem SEGS (mrestrict (w_H W) (ms_mem msf)) (LA + 0) (N.to_nat 8) (hl_v l)).
  { eapply (field_of_region E _ 10 LA); [exact RL3 | exact U10 | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
    cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
  assert (VL8 : val_mem SEGS (mrestrict (w_H W) (ms_mem msf)) (LA + 8) (N.to_nat 4) (hl_n l)).
  { eapply (field_of_region E _ 10 LA); [exact RL3 | exact U10 | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
    cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
  assert (VL12 : val_mem SEGS (mrestrict (w_H W) (ms_mem msf)) (LA + 12) (N.to_nat 4) (hl_cap l)).
  { eapply (field_of_region E _ 10 LA); [exact RL3 | exact U10 | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
    cbn [sv_denot]. rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
  rewrite Z.add_0_r in VL0. rewrite Hbr in VL8.
  assert (HAWR : awr W (ms_mem msf) LA 16).
  { intros i Hi. destruct RL3 as (_ & _ & RLw & _). cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in RLw.
    rewrite U10 in RLw. exact (RLw i Hi). }
  eapply (lf_exit_x W ly S Hp regs mem md ch LA l lines kr W ly S Hp (ms_regs msf) (ms_mem msf) _ 0 HCTX HJ).
  + unfold lf_regsT.
    split; [rewrite F2, Usp; f_equal; lia|].
    split; [rewrite F3, E3; reflexivity|].
    split; [rewrite F4, E4; reflexivity|].
    split; [rewrite F8, E10; reflexivity|].
    split; [rewrite F18, E35; reflexivity|].
    split; [rewrite F20; exact D20|].
    split; [rewrite F25, E25; reflexivity|].
    split; [rewrite F26, E26; reflexivity|].
    rewrite F27, E27; reflexivity.
  + exact FRM0.
  + exact VL0.
  + exact VL8.
  + exact VL12.
  + exact HAWR.
  + intros Hcp. destruct Hvc as [[H0 _] | (_ & Hin & _)]; [lia | exact Hin].
  + intros rest Hpp. unfold lf_blks, list_blks in *. rewrite Hrn in Hpp. cbn [firstn map] in Hpp |- *. exact Hpp.
  + reflexivity.
  + rewrite Hbr, Z.mul_0_l. exact (mle_start MT S MLAW).
  + intros a Hi Hno Herr Hpp. apply (lf_apresent_grows _ _ _ a HGrf). exact (lf_apresent_grows _ _ _ a HGr0 Hpp).
  + intros i Hi. rewrite K5 by lf_err_side ERF i Hi. apply K0; lf_err_side ERF i Hi.
  + eapply (lf_rm_cast RP S _ _ HRM0). rewrite lf_rk, Hrn. reflexivity.
  + exact HCNT0.
- (* n > 0: into the loop *)
  lazymatch goal with Hb : branch_taken _ _ _ = false |- _ => rename Hb into Hbr end.
  rewrite branch_eq_U in Hbr. rewrite (U_atom E 33 (hl_n l) E33) in Hbr by lia.
  rewrite U_SLit, (zcanon_id 0) in Hbr by (unfold M64; lia).
  apply Z.eqb_neq in Hbr.
  assert (Hn0' : (length (hl_recs l) =? 0)%nat = false) by (apply Nat.eqb_neq; unfold hl_n in Hbr; lia).
  paj_run_to_tok_x RUNTO HS HJ SHOK lf_Bspan A_lf_loop.
  { lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
    apply awr_ok_x_cons_awr0; [awr_ok_tac; exact Usp|]. apply awr_ok_x_cons_awr0; [awr_ok_tac|].
    apply awr_ok_x_cons_awr0; [awr_ok_tac|]. apply awr_ok_x_cons_g; [|apply awr_ok_x_nil].
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]. rewrite U10. intros a Ha. apply HLG. lia. }
  lazymatch goal with |- SRr _ _ (mkCfg ?mm _) _ => rename mm into msf end.
  lazymatch goal with Hgr : mem_grows (mrestrict (w_H W) (ms_mem ms0)) (mrestrict (w_H W) (ms_mem msf)) |- _ => rename Hgr into HGrf end.
  lazymatch goal with Hf : frame_of _ _ (mrestrict (w_H W) (ms_mem ms0)) (mrestrict (w_H W) (ms_mem msf)) |- _ => rename Hf into HFrf end.
  lazymatch type of HFrf with frame_of ?Ev ?rs _ _ => let rs' := eval vm_compute in rs in change rs with rs' in HFrf end.
  assert (K5 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 80 <= a < spZ regs) -> ~ (LA <= a < LA + 16) ->
    aview SEGS (w_H W) (ms_mem msf) a = aview SEGS (w_H W) (ms_mem ms0) a).
  { intros a Ha H1 H2. apply (aview_kept_out _ _ (w_H W) (ms_mem ms0) (ms_mem msf) HFrf a Ha).
    intros (rg & Hin & Hr). cbn [In] in Hin. destruct Hin as [<- | [<- | [<- | [<- | []]]]];
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr;
    [rewrite Usp in Hr; lia | lia | lia | rewrite U10 in Hr; lia]. }
  pmkst HS.
  prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4. prreg HS (8%bv : bv 5) F8.
  prreg HS (9%bv : bv 5) F9. prreg HS (18%bv : bv 5) F18. prreg HS (23%bv : bv 5) F23.
  prreg HS (25%bv : bv 5) F25. prreg HS (26%bv : bv 5) F26. prreg HS (27%bv : bv 5) F27.
  prreg_raw HS (19%bv : bv 5) F19. prreg_raw HS (20%bv : bv 5) F20. prreg_raw HS (21%bv : bv 5) F21.
  pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RS0.
  pose proof (st_ok_pi_region_nth _ _ _ 3 _ HS eq_refl) as RL3.
  cbn [ms_mem restrict] in RS0, RL3.
  assert (FRM0 : lf_frame W (ms_mem msf) (spZ regs) regs).
  { intros i Hi. unfold arm.
    pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 (nth i lf_saved 0)))) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
    replace (spZ regs - 80 + 8 * Z.of_nat i) with (spZ regs + (-80 + 8 * Z.of_nat i)) by ring.
    eapply (slot_of_region E _ (spZ regs) _ (-80) 0 (-80) 0 (-80 + 8 * Z.of_nat i) (SOff (Z.to_nat (nth i lf_saved 0)) 0)).
    - exact RS0.
    - exact Usp.
    - clear - Hi. do 10 (destruct i as [|i]; [cbn [In]; repeat first [left; reflexivity | right] |]). lia.
    - cbn [sv_denot]. rewrite (ERS i Hi), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    - exact Hr. }
  assert (VL0 : val_mem SEGS (mrestrict (w_H W) (ms_mem msf)) (LA + 0) (N.to_nat 8) (hl_v l)).
  { eapply (field_of_region E _ 10 LA); [exact RL3 | exact U10 | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
    cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
  assert (VL8 : val_mem SEGS (mrestrict (w_H W) (ms_mem msf)) (LA + 8) (N.to_nat 4) (hl_n l)).
  { eapply (field_of_region E _ 10 LA); [exact RL3 | exact U10 | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
    cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
  assert (VL12 : val_mem SEGS (mrestrict (w_H W) (ms_mem msf)) (LA + 12) (N.to_nat 4) (hl_cap l)).
  { eapply (field_of_region E _ 10 LA); [exact RL3 | exact U10 | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
    cbn [sv_denot]. rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
  rewrite Z.add_0_r in VL0.
  assert (HAWR : awr W (ms_mem msf) LA 16).
  { intros i Hi. destruct RL3 as (_ & _ & RLw & _). cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in RLw.
    rewrite U10 in RLw. exact (RLw i Hi). }
  assert (HVEC : 0 < hl_cap l -> In (hl_v l, AREC * hl_cap l) (ablocks B ly S) /\
    garr8 SEGS (arm W (ms_mem msf)) (hl_v l) (bzs (concat (map text_rec (hl_recs l)) ++ hl_junk l))).
  { intros Hcp. destruct Hvc as [[H0 _] | (_ & Hin & Hjl & Hg)]; [lia|]. split; [exact Hin|].
    destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hin) as (_ & H4096 & Hce & _).
    pose proof (blk_off_imgP_x B ARx LAWS IMGC BLKN _ _ _ _ _ _ _ _ HAR Hin) as Hoff.
    assert (Rq : req_size (AREC * hl_cap l) = 16 * hl_cap l) by (unfold req_size, AREC; destruct (Z.eqb_spec (16 * hl_cap l) 0); lia).
    rewrite Rq in Hce, Hoff. unfold off_img in Hoff.
    assert (Hvlen : Z.of_nat (length (bzs (concat (map text_rec (hl_recs l)) ++ hl_junk l))) = 16 * hl_cap l).
    { unfold bzs. rewrite length_map, length_app, lf_len_text_recs. unfold hl_n, AREC in *. lia. }
    unfold arm in Hg |- *. apply (lf_garr8_kept (w_H W) (w_H W) mem (ms_mem msf)); [|exact Hg].
    intros j Hj. rewrite Hvlen in Hj.
    rewrite K5 by (unfold LF_STK, ASTACK in *; lia). apply K0; unfold LF_STK, ASTACK in *; lia. }
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdf) _ =>
    assert (HINV : lf_inv_x W ly S Hp regs mem md LA l (length (hl_recs l)) kr W ly S Hp (ms_regs msf) (ms_mem msf) mdf 0) end.
  { unfold lf_inv_x.
    split; [exact HJ|].
    split.
    { unfold lf_regs.
      split; [rewrite F2, Usp; f_equal; lia|].
      split; [rewrite F3, E3; reflexivity|].
      split; [rewrite F4, E4; reflexivity|].
      split; [rewrite F8, E10; reflexivity|].
      split; [rewrite F9, U10; reflexivity|].
      split; [rewrite F18, E35; reflexivity|].
      split; [rewrite F19; exact D19|].
      split; [rewrite F20; exact D20|].
      split; [rewrite F21; exact D21|].
      split; [rewrite F23, E33; reflexivity|].
      split; [rewrite F25, E25; reflexivity|].
      split; [rewrite F26, E26; reflexivity|].
      rewrite F27, E27; reflexivity. }
    split; [exact FRM0|]. split; [exact VL0|]. split; [exact VL8|]. split; [exact VL12|]. split; [exact HAWR|].
    split; [exact HVEC|].
    split; [rewrite firstn_all; rewrite Forall_forall in HFA |- *; intros r Hr; exact (proj1 (HFA r Hr))|].
    split; [intros rest Hpp; unfold lf_blks; rewrite firstn_all; exact Hpp|].
    split; [reflexivity|].
    split; [unfold hl_n; rewrite Z.sub_diag, Z.mul_0_l; exact (mle_start MT S MLAW)|].
    split; [intros a Hi Hno Herr Hpp; apply (lf_apresent_grows _ _ _ a HGrf); exact (lf_apresent_grows _ _ _ a HGr0 Hpp)|].
    split.
    { intros i Hi. rewrite K5 by lf_err_side ERF i Hi. apply K0; lf_err_side ERF i Hi. }
    split; [|exact HCNT0].
    eapply (lf_rm_cast RP S _ _ HRM0). rewrite lf_rk. lia. }
  pose proof (IND _ _ _ _ _ _ _ _ _ (le_n _) HINV) as HH. rewrite Hn0' in HH. exact HH.
Qed.
(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): the walk at a world relation R.  The journal ajournal_gx_x becomes
   ajournal_gx_xR R, SRr SEGS becomes SRrG SEGS R, the post lf_post_x becomes lf_post_xR R (W_contract_srlf_xR.v), and
   the continuation binders run over R.  Both free calls (the loop's, returning to list_free + 0x98; the exit's free /
   free(NULL), returning to list_free + 0xf8) go through the R forms of the free rules (W_journal_x.v Section hc:
   afree_cf_rule_c_xR / afree_null_cf_rule_c_xR), which also take the call-boundary premise RO on the call memory
   (part 3c removed their memnorm premise): RO_ARx gives it from the inner journal's ARx at the call state (as
   W_gse_tail.v gt_free_xR).  The
   straight-line runs are the G runs (paj_run_x_xG / paj_run_to_x_xG, concluding SRrG SEGS R), the branches
   paj_branch_xR, the __asan_memmove call aj_gx_entry_at_xR (its contract AMOVE stays strict, lifted by WLE_R), and the
   return paj_ret_at after SRr_SRrG (WLE_R); composition is SRrG_bind (R_trans).  The strict lf_iter_x, lf_exit_x,
   lf_exit_inv_x and pb_list_free_x above keep their proofs. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Variable RO : (word -> option byte) -> Prop.
Hypothesis RO_ARx : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> RO mem.
Hypothesis AFREE_R : afree_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX R.
Hypothesis AFREEN_R : afree_null_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX R.
Let RUNG := paj_run_x_xG B PST ARx LAWS R G HG 0 [].
Let RUNTOG := paj_run_to_x_xG B PST ARx LAWS R G HG 0 [].
Let BRG := paj_branch_xR (PI := PI) (R := R).
(* :684 lf_inv_x *)
Definition lf_inv_xR (W : world SEGS) ly S (Hp : list Z) regs0 mem0 md0 (LA : Z) (l : hlist) (c kr : nat)
(Wc : world SEGS) lyc Sc (Hpc : list Z) (regs : bvmap 5 word) memc mdc (kk : Z) : Prop :=
ajournal_gx_xR SEGS B PST ARx R G 0 [] LF_STK (spZ regs0) (blk_FP (list_blks l)) ly S Hp W mem0 md0 [] lyc Sc Hpc Wc memc mdc kk /\
lf_regs regs regs0 LA (Z.of_nat c) /\ lf_frame Wc memc (spZ regs0) regs0 /\
val_mem SEGS (arm Wc memc) LA 8 (hl_v l) /\ val_mem SEGS (arm Wc memc) (LA + 8) 4 (Z.of_nat c) /\
val_mem SEGS (arm Wc memc) (LA + 12) 4 (hl_cap l) /\ awr Wc memc LA 16 /\
(0 < hl_cap l -> In (hl_v l, AREC * hl_cap l) (ablocks B lyc Sc) /\
  garr8 SEGS (arm Wc memc) (hl_v l) (bzs (concat (map text_rec (hl_recs l)) ++ hl_junk l))) /\
Forall (fun r => In (fst r, Z.of_nat (length (snd r)) + 1) (ablocks B lyc Sc)) (firstn c (hl_recs l)) /\
(forall rest, Permutation (ablocks B ly S) (list_blks l ++ rest) -> Permutation (ablocks B lyc Sc) (lf_blks l c ++ rest)) /\
frames Sc = frames S /\ mo_le MT S Sc ((hl_n l - Z.of_nat c) * mo_free MT) /\ apres_kept B W mem0 Wc memc /\
(forall i, 0 <= i < 4 -> aview SEGS (w_H Wc) memc (as_errno B + i) = aview SEGS (w_H W) mem0 (as_errno B + i)) /\
rp_RM RP Sc (c + 1 + kr) /\ cnt_ok RP (ablocks B lyc Sc).
(* :701 lf_iter_x *)
Lemma lf_iter_xR : forall (c : nat) W ly S Hp regs0 mem0 md0 ch LA (l : hlist) lines kr Wc lyc Sc Hpc regs memc mdc kk,
lf_ctx_x W ly S Hp regs0 mem0 md0 ch LA l lines -> (1 <= c <= length (hl_recs l))%nat ->
lf_inv_xR W ly S Hp regs0 mem0 md0 LA l c kr Wc lyc Sc Hpc regs memc mdc kk ->
(forall Wc' lyc' Sc' Hpc' regs' memc' mdc' kk', lf_inv_xR W ly S Hp regs0 mem0 md0 LA l (c - 1) kr Wc' lyc' Sc' Hpc' regs' memc' mdc' kk' ->
  SRrG SEGS R Wc' (mkCfg (mkst regs' (Z_to_bv 64 (BASE + if (c - 1 =? 0)%nat then A_lf_done else A_lf_loop)) memc' (seg_rom SEGS)) mdc')
  (lf_post_xR B PST ARx R MT RP G regs0 ly S Hp W mem0 md0 LA l lines kr)) ->
SRrG SEGS R Wc (mkCfg (mkst regs (Z_to_bv 64 (BASE + A_lf_loop)) memc (seg_rom SEGS)) mdc) (lf_post_xR B PST ARx R MT RP G regs0 ly S Hp W mem0 md0 LA l lines kr).
Proof.
intros c W ly S Hp regs0 mem0 md0 ch LA l lines kr Wc lyc Sc Hpc regs memc mdc kk HCTX Hc HINV HK.
destruct HCTX as (HPRE & HL & HLG & HZS & HROM & HMO).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof (lf_LA_range LA HLG) as (HLA1 & HLA2 & _ & _ & HLAe).
pose proof (lf_errno_facts (spZ regs0) LA ltac:(clear - Hceil Hslo; lia) HLG) as ERF.
destruct HINV as (HJ & HR & Hfr & Mv & Mn & Mc & Hw & HVEC & HTX & HPERM & HFRS & HMLE & HAPK & HERR & HRM & HCNT).
pose proof HL as (_ & _ & _ & _ & (Hn0 & Hcap) & Hvc & Hnd & Hnv & HFA).
assert (Hcap0 : 0 < hl_cap l) by (clear - Hc Hn0; unfold hl_n in Hn0; lia).
destruct (HVEC Hcap0) as (Hvin & Hvg).
pose proof (ajournal_gx_AR_xR SEGS B PST ARx G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARc.
set (r := nth (c - 1) (hl_recs l) (0, [])).
assert (Hfl : firstn c (hl_recs l) = firstn (c - 1) (hl_recs l) ++ [r]).
{ subst r. clear -Hc. destruct c as [|c0]; [lia|]. cbn [Nat.sub]. rewrite Nat.sub_0_r. apply lf_firstn_last. lia. }
assert (Hrin : In r (firstn c (hl_recs l))) by (rewrite Hfl; apply in_or_app; right; left; reflexivity).
assert (Hrin' : In r (hl_recs l)) by (rewrite <- (firstn_skipn c (hl_recs l)); apply in_or_app; left; exact Hrin).
assert (Hrb : In (fst r, Z.of_nat (length (snd r)) + 1) (ablocks B lyc Sc)) by (exact (proj1 (Forall_forall _ _) HTX r Hrin)).
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HARc Hrb) as (Hs16 & Hs4096 & Hsce & _).
assert (Hsr : 4096 <= fst r /\ fst r + Z.of_nat (length (snd r)) + 1 <= alloc_ceiling).
{ clear - Hsce Hs4096. unfold req_size in Hsce. destruct (Z.eqb_spec (Z.of_nat (length (snd r)) + 1) 0); lia. }
pose proof (lf_slot_val _ _ _ _ (c - 1) Hvg ltac:(clear - Hc; lia)) as Ms. fold r in Ms.
rewrite unsigned_lit_small in Ms by (unfold alloc_ceiling in *; lia).
replace (16 * Z.of_nat (c - 1)) with (16 * (Z.of_nat c - 1)) in Ms by (clear - Hc; lia).
assert (Hsp0 : lf_sp0 (spZ regs0)) by (split; [exact Hal16 | clear - Hceil Hslo Hshi H47; unfold LF_STK, ASTACK in *; lia]).
assert (Hc1 : 1 <= Z.of_nat c <= hl_cap l) by (clear - Hc Hn0; unfold hl_n in Hn0; lia).
assert (Hsr64 : 0 <= fst r < 2 ^ 64) by (unfold alloc_ceiling in *; lia).
pose proof Hsp0 as (Hsp0a & Hsp0b & Hsp0c).
assert (Rq : req_size (AREC * hl_cap l) = 16 * hl_cap l) by (unfold req_size, AREC; destruct (Z.eqb_spec (16 * hl_cap l) 0); lia).
pose proof (blk_off_imgP_x B ARx LAWS IMGC BLKN _ _ _ _ _ _ _ _ HARc Hvin) as Hvimg. rewrite Rq in Hvimg. unfold off_img in Hvimg.
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HARc Hvin) as (Hv16 & Hv4096 & Hvce & _). rewrite Rq in Hvce.
assert (Hv64 : 0 <= hl_v l < 2 ^ 48) by (unfold alloc_ceiling in *; lia).
assert (Hjl : Z.of_nat (length (hl_junk l)) = AREC * (hl_cap l - hl_n l))
by (destruct Hvc as [[H0 _] | (_ & _ & Hj & _)]; [lia | exact Hj]).
assert (Hvlen : Z.of_nat (length (bzs (concat (map text_rec (hl_recs l)) ++ hl_junk l))) = 16 * hl_cap l).
{ unfold bzs. rewrite length_map, length_app, lf_len_text_recs. unfold hl_n, AREC in *. lia. }
assert (Hsv : fst r <> hl_v l) by (intros He; apply Hnv; rewrite <- He; apply in_map; exact Hrin').
assert (Hvne : (hl_v l, AREC * hl_cap l) <> (fst r, Z.of_nat (length (snd r)) + 1))
by (intros He; injection He as He1 _; exact (Hsv (eq_sym He1))).
assert (Dvs : hl_v l + 16 * hl_cap l <= fst r \/ fst r + req_size (Z.of_nat (length (snd r)) + 1) <= hl_v l).
{ pose proof (sep_blocks_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc _ _ _ _ HARc Hvin Hrb Hvne) as D. rewrite Rq in D.
  unfold zdisjoint in D. cbn [fst snd] in D. exact D. }
destruct (lf_head_loop_x Wc lyc Sc Hpc memc mdc regs regs0 LA (hl_v l) (hl_cap l) (Z.of_nat c) (fst r) HARc HR
  Hsp0 Hfr HLA1 HLA2 HZS Mv Mn Mc Hw Hc1 Hcap Hvin Ms Hsr64) as [HS SHOK].
remember (Eimg (Ereg regs (lf_xl (hl_v l) (hl_cap l) (fst r) (hl_v l + 16 * (Z.of_nat c - 1)) regs0))) as E eqn:HE in HS.
rewrite <- HE in SHOK.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
destruct HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R21 & R23 & R25 & R26 & R27).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs0 - 80).
{ rewrite E2, R2. apply unsigned_lit_small. destruct Hsp0 as (Hm & H1 & H2). unfold alloc_ceiling in H1. lia. }
assert (E3 : ew E 3 = getr regs0 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 3 3%bv eq_refl); exact R3).
assert (E4 : ew E 4 = getr regs0 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 4 4%bv eq_refl); exact R4).
assert (E25 : ew E 25 = getr regs0 25) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact R25).
assert (E26 : ew E 26 = getr regs0 26) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact R26).
assert (E27 : ew E 27 = getr regs0 27) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact R27).
assert (E8 : ew E 8 = Z_to_bv 64 LA) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 8 8%bv eq_refl); exact R8).
assert (E18 : ew E 18 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact R18).
assert (E23 : ew E 23 = Z_to_bv 64 (Z.of_nat c)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 23 23%bv eq_refl); exact R23).
assert (E32 : ew E 32 = Z_to_bv 64 (hl_v l)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (hl_cap l)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E44 : ew E 44 = Z_to_bv 64 (fst r)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 12)).
assert (E45 : ew E 45 = Z_to_bv 64 (hl_v l + 16 * (Z.of_nat c - 1))) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 13)).
assert (ESV : forall i, (i < 10)%nat -> ew E (34 + i) = getr regs0 (Z_to_bv 5 (nth i lf_saved 0)))
by (intros i Hi; subst E; exact (lf_ew_saved regs regs0 _ _ _ _ i Hi)).
assert (U8 : bv_unsigned (ew E 8) = LA) by (rewrite E8; apply unsigned_lit_small; lia).
assert (HAE : env_agree 32 (Ereg regs (lf_xl (hl_v l) (hl_cap l) (fst r) (hl_v l + 16 * (Z.of_nat c - 1)) regs0)) E)
by (subst E; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HMLE' : mo_le MT S Sc ((hl_n l - Z.of_nat c) * mo_free MT)) by exact HMLE.
assert (HMOf : mo_ok MT Sc (mo_free MT)).
{ eapply (mok_station MT S Sc (lf_cost MT l) _ (mo_free MT) MLAW HMO HMLE'); [pose proof (mo_free_nonneg MT MLAW); lia|].
  unfold lf_cost, hl_n. pose proof (mo_free_nonneg MT MLAW) as Hf.
  assert (Hcn : Z.of_nat c <= Z.of_nat (length (hl_recs l))) by (clear - Hc Hn0; unfold hl_n in Hn0; lia).
  clear - Hf Hcn. nia. }
paj_run_tok_xR RUNG HS HJ SHOK lf_Bspan.
{ apply awr_ok_x_cons_awr0; [awr_ok_tac; exact Usp|]. apply awr_ok_x_cons_g; [|apply awr_ok_x_cons_awr0; [awr_ok_tac|apply awr_ok_x_nil]].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi lf_lregL lf_lreg base_val]. subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs _ 8 8%bv eq_refl), R8, unsigned_lit_small by lia. intros a Ha. apply HLG. lia. }
(* free(v[c-1].s) *)
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.
destruct HJ as (HSTK & HXO & (memS & HJi & Hag) & Hout). rewrite !Z.add_0_r in HJi.
pose proof (proj1 HJi) as HARm.
pose proof (RO_ARx _ _ _ _ _ _ HARm) as HROm.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (LA <= a < LA + 16) -> aview SEGS (w_H Wc) (ms_mem ms) a = aview SEGS (w_H Wc) memc a).
{ intros a Ha Hno. lazymatch goal with Hf : frame_of _ _ (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) (ms_mem ms)) |- _ =>
    apply (aview_kept_out _ _ (w_H Wc) memc (ms_mem ms) Hf a Ha) end.
  intros (rg & Hin & Hr). cbn [ss_mem ss_lfL In] in Hin. destruct Hin as [<- | [<- | [<- | []]]];
  cbn [lf_stackL lf_lregL lf_lreg lf_slotL YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr;
  [lia | rewrite U8 in Hr; lia | lia]. }
assert (Usp2 : spZ (ms_regs ms) = spZ regs0 + -80).
{ unfold spZ at 1. rewrite Q2. rewrite Usp. lia. }
assert (R10s : getr (ms_regs ms) 10 = w64 (fst r)).
{ rewrite Q10. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 12). }
assert (HGP : getr (ms_regs ms) 3 = w64 (as_gp B)).
{ rewrite Q3. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 3 3%bv eq_refl), R3. exact Hgp. }
assert (HTP : getr (ms_regs ms) 4 = w64 (as_tp B)).
{ rewrite Q4. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 4 4%bv eq_refl), R4. exact Htp. }
assert (HS0 : s0Z (ms_regs ms) = LA).
{ unfold s0Z. rewrite Q8. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 8 8%bv eq_refl), R8. apply unsigned_lit_small. lia. }
assert (HCH : chain_pre lyc (aview SEGS (w_H Wc) (ms_mem ms)) (ms_regs ms) []).
{ unfold chain_pre. split; [unfold raZ; rewrite Q1; rewrite unsigned_lit_small by lia; lia|].
  destruct (frame0_ok lyc (ms_regs ms)); [|reflexivity].
  replace (bad_next (spZ (ms_regs ms)) (ly_top lyc) (s0Z (ms_regs ms))) with true; [reflexivity|].
  symmetry. unfold bad_next. rewrite HS0, Usp2. apply orb_true_iff. left. apply orb_true_iff. left. apply Z.leb_le. lia. }
(* the free's caller context: the chain is [] (s0 = LA, an image address), the trace the singleton [list_free + 0x98] *)
assert (HCTXL : In (raZ (ms_regs ms) :: spine []) CTX).
{ cbn [spine map]. replace (raZ (ms_regs ms)) with (BASE + AF_fr_list_free + 0x98); [exact HCTX_lf_loop|].
  unfold raZ. rewrite Q1, unsigned_lit_small by lia. first [lia | unfold AF_fr_list_free in *; lia]. }
rewrite HBfree.
assert (HRMc : rp_RM RP Sc (1 + (c - 1 + 1 + kr))) by (apply (lf_rm_cast RP Sc _ _ HRM); clear - Hc; lia).
eapply (SRrG_bind SEGS R R_trans).
{ exact (AFREE_R Wc (ms_regs ms) (ms_mem ms) LF_STK (spZ regs0) (blk_FP (list_blks l)) ly S Hp W memS md0 [] lyc Sc Hpc _ _
      (fst r) (Z.of_nat (length (snd r)) + 1) (-80) (getr (ms_regs ms) 1) [] (c - 1 + 1 + kr)%nat HJi Hrb R10s Usp2 eq_refl ltac:(lia)
      ltac:(unfold LF_STK, ASTACK; lia)
      (aj_stack_room_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (-80) (ms_regs ms) HJi Usp2 ltac:(unfold LF_STK, ASTACK; lia))
      HGP HTP eq_refl ltac:(rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]) HCH HROm HCTXL
      HRMc HCNT
      ltac:(intros _ i Hi; apply (inFP_ablocks_fp (list_blks l) (fst r) (Z.of_nat (length (snd r)) + 1) i);
            [unfold list_blks; apply in_or_app; right; apply (in_map (fun r0 => (fst r0, Z.of_nat (length (snd r0)) + 1))); exact Hrin' | exact Hi]) HMOf). }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & -> & HJ2i & HP2 & (b1 & b2 & Eb1 & Eb2) & HFR2 & HK2 & HML2 & HRM2 & HER2 & HPR2).
rewrite Q1.
pose proof (proj1 HJ2i) as HAR2.
assert (HJ2 : ajournal_gx_xR SEGS B PST ARx R G 0 [] LF_STK (spZ regs0) (blk_FP (list_blks l)) ly S Hp W mem0 md0 [] ly2 S2 Hp2 W2 mem2 md2 (kk + 1)).
{ apply (ajournal_gx_pack_xR SEGS B PST ARx G 0 [] LF_STK (spZ regs0) _ ly S Hp W mem0 md0 [] ly2 S2 Hp2 W2 mem2 md2 (kk + 1) memS HSTK HXO);
  [rewrite !Z.add_0_r; exact HJ2i | exact Hag | apply out_none]. }
(* ---- the bookkeeping of the free: the vector and the other texts stay, the text r goes ---- *)
assert (Hvin2 : In (hl_v l, AREC * hl_cap l) (ablocks B ly2 S2)) by (rewrite Eb2; exact (lf_in_drop _ _ b1 b2 _ Eb1 Hvin Hvne)).
assert (HndL : List.NoDup (map fst (hl_recs l))) by (apply (proj1 (stdpp.base.NoDup_ListNoDup _)); exact Hnd).
assert (Hnr : ~ In (fst r) (map fst (firstn (c - 1) (hl_recs l)))).
{ rewrite <- (firstn_skipn c (hl_recs l)) in HndL. rewrite map_app in HndL. apply List.NoDup_app_remove_r in HndL.
  rewrite Hfl, map_app in HndL. cbn [map] in HndL. intros Hin.
  apply (List.NoDup_remove_2 (map fst (firstn (c - 1) (hl_recs l))) [] (fst r)); [exact HndL | rewrite app_nil_r; exact Hin]. }
assert (HTX2 : Forall (fun r0 => In (fst r0, Z.of_nat (length (snd r0)) + 1) (ablocks B ly2 S2)) (firstn (c - 1) (hl_recs l))).
{ rewrite Forall_forall in HTX |- *. intros r0 Hr0. rewrite Eb2. apply (lf_in_drop _ _ b1 b2 _ Eb1).
  - apply HTX. rewrite Hfl. apply in_or_app. left. exact Hr0.
  - intros He. injection He as He1 _. apply Hnr. rewrite <- He1. apply in_map. exact Hr0. }
assert (HPERM2 : forall rest, Permutation (ablocks B ly S) (list_blks l ++ rest) ->
  Permutation (ablocks B ly2 S2) (lf_blks l (c - 1) ++ rest)).
{ intros rest Hpp. pose proof (HPERM rest Hpp) as Hp1. rewrite Eb1 in Hp1. rewrite Eb2.
  unfold lf_blks in Hp1 |- *. rewrite Hfl, map_app in Hp1. cbn [map] in Hp1.
  exact (lf_perm_drop2 b1 b2 _ _ rest _ Hp1). }
assert (HML2' : mo_le MT S S2 ((hl_n l - Z.of_nat (c - 1)) * mo_free MT)).
{ assert (E1c : Z.of_nat (c - 1) = Z.of_nat c - 1) by (clear - Hc; lia). rewrite E1c.
  replace ((hl_n l - (Z.of_nat c - 1)) * mo_free MT) with ((hl_n l - Z.of_nat c) * mo_free MT + mo_free MT) by ring.
  exact (mle_station MT S Sc S2 _ _ MLAW HMLE' HML2). }
assert (HFRS2 : frames S2 = frames S) by (rewrite HFR2; exact HFRS).
assert (HCNT2 : cnt_ok RP (ablocks B ly2 S2)).
{ rewrite Eb2. apply (lf_cnt_del RP b1 (fst r, Z.of_nat (length (snd r)) + 1) b2). rewrite <- Eb1. exact HCNT. }
lazymatch goal with Hgr : mem_grows (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) (ms_mem ms)) |- _ =>
  assert (PR1 : forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) (ms_mem ms) a)
  by (intros a Hpp; exact (lf_apresent_grows (w_H Wc) memc (ms_mem ms) a Hgr Hpp)) end.
assert (HAPK2 : apres_kept B W mem0 W2 mem2).
{ intros a Hi Hno Herr Hpp.
  assert (Hnot : forall ly0 S0 Hp0 (W0 : world SEGS) m0 md0', ARx ly0 S0 Hp0 W0 m0 md0' -> ~ aowned B ly0 S0 a)
  by (intros ly0 S0 Hp0 W0 m0 md0' HA Ho; apply Hno; exact (proj1 (alx_owned_image _ _ _ LAWS ly0 S0 Hp0 W0 m0 md0' a HA Hi) Ho)).
  apply (HPR2 a Hi (Hnot _ _ _ _ _ _ HARm) (Hnot _ _ _ _ _ _ HAR2) Herr); [|exact (PR1 a (HAPK a Hi Hno Herr Hpp))].
  intros Hb. exact (blk_img_x SEGS B ARx LAWS lyc Sc Hpc Wc (ms_mem ms) _ _ _ a HARm Hrb Hb Hi). }
(* ---- after the free: keep the frame and the list struct (no slot) ---- *)
assert (HLAimg : forall a, LA <= a < LA + 16 ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4))
by (intros a Ha; exact (conj (proj1 (HG a (HLG a Ha))) (conj (proj1 (proj2 (HG a (HLG a Ha)))) (proj1 (HGR a (HLG a Ha)))))).
assert (KF : forall a, LA <= a < LA + 16 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) (ms_mem ms) a).
{ intros a Ha. destruct (HLAimg a Ha) as (Hi & Ho & He). destruct HK2 as (_ & _ & K3 & _). exact (K3 a Hi Ho He). }
assert (KFs : forall a, spZ regs0 - 80 <= a < spZ regs0 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) (ms_mem ms) a).
{ intros a Ha. destruct HK2 as (Kh & _). apply Kh; [destruct Hsp0 as (_ & H1 & H2); lia | lia]. }
assert (KFw : forall a, LA <= a < LA + 16 ->
  writable_at SEGS (mrestrict (w_H Wc) (ms_mem ms)) a -> writable_at SEGS (mrestrict (w_H W2) mem2) a).
{ intros a Ha. destruct (HLAimg a Ha) as (Hi & Ho & He). apply (lf_writable_img Wc W2 (ms_mem ms) mem2 a Hi).
  intros Hpp. apply (HPR2 a Hi); [| | exact He | | exact Hpp].
  - intros Hao. apply Ho. exact (proj1 (alx_owned_image _ _ _ LAWS _ _ _ _ _ _ a HARm Hi) Hao).
  - intros Hao. apply Ho. exact (proj1 (alx_owned_image _ _ _ LAWS _ _ _ _ _ _ a HAR2 Hi) Hao).
  - intros Hb. exact (blk_img_x SEGS B ARx LAWS lyc Sc Hpc Wc (ms_mem ms) _ _ _ a HARm Hrb Hb Hi). }
jafter_call_keep_pi HS 46%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0; 1]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - apply (lf_region_kept2 E Wc W2 (ms_mem ms) mem2 2 (spZ regs0 - 80)); [exact Usp | intros a Ha; apply KFs; lia | intros a Ha; exfalso; lia].
  - apply (lf_region_kept2 E Wc W2 (ms_mem ms) mem2 8 LA); [exact U8 | intros a Ha; apply KF; lia | intros a Ha; apply KFw; lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 46 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 46)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
clear HEa.
assert (SHOK2 : sh_ok SEGS lf_BxL lf_SHT Ea (mrestrict (w_H W2) mem2)).
{ unfold sh_ok, lf_SHT. constructor; [|constructor].
  apply (lf_shent8_x Ea ly2 S2 Hp2 W2 mem2 md2 LA HAR2 HZS); [rewrite OLDa by lia; exact E8 | rewrite OLDa by lia; exact E18 | exact HLA1 | exact HLA2]. }
assert (Uspa : bv_unsigned (ew Ea 2) = spZ regs0 - 80) by (rewrite OLDa by lia; exact Usp).
assert (U8a : bv_unsigned (ew Ea 8) = LA) by (rewrite OLDa by lia; exact U8).
(* ---- 0x86118 .. the jal to __asan_memmove ---- *)
paj_run_tok_xR RUNG HS HJ2 SHOK2 lf_Bspan.
{ apply awr_ok_x_cons_awr0; [awr_ok_tac; exact Uspa|]. apply awr_ok_x_cons_g; [|apply awr_ok_x_nil].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]. rewrite U8a. intros a Ha. apply HLG. lia. }
lazymatch goal with |- SRrG _ _ _ (mkCfg ?mm _) _ => rename mm into ms2 end.
lazymatch goal with Hgr : mem_grows (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) (ms_mem ms2)) |- _ =>
  assert (PR2 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms2) a)
  by (intros a Hpp; exact (lf_apresent_grows (w_H W2) mem2 (ms_mem ms2) a Hgr Hpp)) end.
lazymatch goal with Hf : frame_of _ _ (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) (ms_mem ms2)) |- _ => rename Hf into HFr2 end.
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (LA <= a < LA + 16) -> aview SEGS (w_H W2) (ms_mem ms2) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hno. apply (aview_kept_out _ _ (w_H W2) mem2 (ms_mem ms2) HFr2 a Ha).
  intros (rg & Hin & Hr). cbn [In] in Hin. destruct Hin as [<- | [<- | []]];
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr; [lia | rewrite U8a in Hr; lia]. }
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
pose proof (ajournal_gx_AR_xR SEGS B PST ARx G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2m.
assert (Usp3 : spZ (ms_regs ms2) = spZ regs0 + -80) by (unfold spZ at 1; rewrite P2, Uspa; lia).
assert (HGP2 : getr (ms_regs ms2) 3 = w64 (as_gp B)) by (rewrite P3, OLDa by lia; rewrite E3; exact Hgp).
assert (HTP2 : getr (ms_regs ms2) 4 = w64 (as_tp B)) by (rewrite P4, OLDa by lia; rewrite E4; exact Htp).
assert (HROM2 : rom_view SEGS W2 (ms_mem ms2))
by (exact (ajournal_gx_rom_view_xR SEGS B PST ARx LAWS pa_segs_low G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 HRO PSTR HROM)).
(* __asan_memmove(v + 16 (c - 1), v + 16 c, 0) *)
eapply (SRrG_bind SEGS R R_trans).
{ apply (aj_gx_entry_at_xR B PST ARx LAWS R_trans WLE_R G 0 [] ESTACK (SIGMA WS_asan_memmove)
    (fun a => hl_v l + 16 * (Z.of_nat c - 1) <= a < hl_v l + 16 * (Z.of_nat c - 1) + 0)
    (fun regs' mem' => getr regs' 10 = w64 (hl_v l + 16 * (Z.of_nat c - 1)) /\
       forall i, 0 <= i < 0 -> aview SEGS (w_H W2) mem' (hl_v l + 16 * (Z.of_nat c - 1) + i) =
         aview SEGS (w_H W2) (ms_mem ms2) (hl_v l + 16 * (Z.of_nat c - 1) + 16 + i))
    W2 (ms_regs ms2) (ms_mem ms2) LF_STK (spZ regs0) (blk_FP (list_blks l)) ly S Hp W mem0 md0 [] ly2 S2 Hp2 _ (kk + 1) (-80) (getr (ms_regs ms2) 1) HG eq_refl HJ2).
  - exact Usp3.
  - reflexivity.
  - lia.
  - unfold ESTACK. lia.
  - unfold ESTACK, LF_STK, ASTACK. lia.
  - exact HGP2.
  - exact HTP2.
  - reflexivity.
  - rewrite P1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a. right. cbv beta. lia.
  - intros a Ha. exfalso. cbv beta in Ha. lia.
  - intros a Ha. exfalso. cbv beta in Ha. lia.
  - intros HPRE2 HSC2.
    exact (AMOVE ly2 S2 Hp2 W2 (ms_regs ms2) (ms_mem ms2) _ (hl_v l + 16 * (Z.of_nat c - 1)) (hl_v l + 16 * (Z.of_nat c - 1) + 16) 0 HPRE2
      ltac:(rewrite P10, OLDa by lia; exact E45)
      ltac:(rewrite P11, OLDa by lia; rewrite E45, unsigned_lit_small by (unfold alloc_ceiling in *; lia); reflexivity)
      ltac:(rewrite P12; reflexivity)
      ltac:(lia) ltac:(unfold alloc_ceiling in *; lia) ltac:(unfold alloc_ceiling in *; lia)
      ltac:(intros a Ha; exfalso; lia)
      ltac:(eapply (YCe5x.amem_range_of_block_x SEGS B ARx LAWS ly2 S2 Hp2 W2 (ms_mem ms2) _ (hl_v l) (AREC * hl_cap l)); [exact HAR2m | exact Hvin2 | lia | rewrite Rq; lia])
      ltac:(intros y Hy; exfalso; lia) ltac:(intros H0; exfalso; lia)
      ltac:(lia) ltac:(unfold alloc_ceiling in *; lia)
      ltac:(intros a Ha; exfalso; lia)
      ltac:(eapply (YCe5x.amem_range_of_block_x SEGS B ARx LAWS ly2 S2 Hp2 W2 (ms_mem ms2) _ (hl_v l) (AREC * hl_cap l)); [exact HAR2m | exact Hvin2 | lia | rewrite Rq; lia])
      ltac:(intros y Hy; exfalso; lia) ltac:(intros H0; exfalso; lia)
      HROM2 ltac:(intros H0; exfalso; lia) ltac:(intros a Ha; exfalso; lia)). }
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & (Hd10 & _) & Hfr3 & Hpres3).
rewrite P1.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs0 - 80 - ESTACK <= a < spZ regs0 - 80) ->
  aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) (ms_mem ms2) a).
{ intros a Ha Hs. apply Hfr3; [exact Ha | cbv beta; lia | lia]. }
jafter_call_keep_pi HS 62%nat regs3 (mrestrict (w_H W2) mem3) HP3 [0; 1]%nat HS3.
match type of HS3 with ?ty -> _ => assert (HRK : ty); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - apply (region_kept_aview Ea (w_H W2) (ms_mem ms2) mem3 2 (spZ regs0 - 80)); [exact Uspa | | exact Hpres3].
    intros a Ha. apply KM; [destruct Hsp0 as (_ & H1 & H2); unfold alloc_ceiling in H1; lia | unfold ESTACK; lia].
  - apply (region_kept_aview Ea (w_H W2) (ms_mem ms2) mem3 8 LA); [exact U8a | | exact Hpres3].
    intros a Ha. apply KM; [lia | destruct Hsp0 as (_ & H1 & H2); unfold alloc_ceiling, ESTACK in *; lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc Ea 62 (map (getr regs3) CLOB)) as Eb eqn:HEb in HS.
assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEIa | cbv; lia]).
assert (OLDb : forall m, (m < 62)%nat -> ew Eb m = ew Ea m) by (intros m Hm; rewrite HEb; apply YN3v.ew_havoc_old; exact Hm).
clear HEb.
pose proof (ajournal_gx_AR_xR SEGS B PST ARx G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR3.
assert (SHOK3 : sh_ok SEGS lf_BxL lf_SHT Eb (mrestrict (w_H W2) mem3)).
{ unfold sh_ok, lf_SHT. constructor; [|constructor].
  apply (lf_shent8_x Eb ly2 S2 Hp2 W2 mem3 md3 LA HAR3 HZS);
  [rewrite OLDb, OLDa by lia; exact E8 | rewrite OLDb, OLDa by lia; exact E18 | exact HLA1 | exact HLA2]. }
assert (Uspb : bv_unsigned (ew Eb 2) = spZ regs0 - 80) by (rewrite OLDb by lia; exact Uspa).
assert (U8b : bv_unsigned (ew Eb 8) = LA) by (rewrite OLDb by lia; exact U8a).
(* ---- 0x86144 .. the bnez: l->n = c - 1 ---- *)
paj_run_tok_xR RUNG HS HJ3 SHOK3 lf_Bspan.
{ apply awr_ok_x_cons_awr0; [awr_ok_tac; exact Uspb|]. apply awr_ok_x_cons_g; [|apply awr_ok_x_nil].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]. rewrite U8b. intros a Ha. apply HLG. lia. }
lazymatch goal with |- SRrG _ _ _ (mkCfg ?mm _) _ => rename mm into ms3 end.
lazymatch goal with Hf : frame_of _ _ (mrestrict (w_H W2) mem3) (mrestrict (w_H W2) (ms_mem ms3)) |- _ => rename Hf into HFr3 end.
lazymatch goal with Hgr : mem_grows (mrestrict (w_H W2) mem3) (mrestrict (w_H W2) (ms_mem ms3)) |- _ =>
  assert (PR3 : forall a, apresent (w_H W2) mem3 a -> apresent (w_H W2) (ms_mem ms3) a)
  by (intros a Hpp; exact (lf_apresent_grows (w_H W2) mem3 (ms_mem ms3) a Hgr Hpp)) end.
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (LA <= a < LA + 16) -> aview SEGS (w_H W2) (ms_mem ms3) a = aview SEGS (w_H W2) mem3 a).
{ intros a Ha Hno. apply (aview_kept_out _ _ (w_H W2) mem3 (ms_mem ms3) HFr3 a Ha).
  intros (rg & Hin & Hr). cbn [In] in Hin. destruct Hin as [<- | [<- | []]];
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr; [lia | rewrite U8b in Hr; lia]. }
(* the vector's bytes are the ones at the loop head *)
assert (VEC : forall a, hl_v l <= a < hl_v l + 16 * hl_cap l -> aview SEGS (w_H W2) (ms_mem ms3) a = aview SEGS (w_H Wc) memc a).
{ intros a Ha. assert (HnLA : ~ (LA <= a < LA + 16)) by lia.
  rewrite K3 by (first [exact HnLA | unfold alloc_ceiling in *; lia]).
  rewrite KM by (unfold ESTACK, LF_STK, ASTACK in *; lia).
  rewrite K2 by (first [exact HnLA | unfold alloc_ceiling in *; lia]).
  replace a with (hl_v l + (a - hl_v l)) by ring.
  destruct HK2 as (_ & KB & _). rewrite (KB (hl_v l) (AREC * hl_cap l) (a - hl_v l) Hvin) by (rewrite ?Rq; cbv beta; lia).
  replace (hl_v l + (a - hl_v l)) with a by ring. apply K1; [unfold alloc_ceiling in *; lia | exact HnLA]. }
assert (PRS : apres_kept B W mem0 W2 (ms_mem ms3)).
{ intros a Hi Hno Herr Hpp. apply PR3. apply Hpres3. apply PR2. exact (HAPK2 a Hi Hno Herr Hpp). }
assert (ERR3 : forall i, 0 <= i < 4 -> aview SEGS (w_H W2) (ms_mem ms3) (as_errno B + i) = aview SEGS (w_H W) mem0 (as_errno B + i)).
{ intros i Hi. rewrite K3 by lf_err_side ERF i Hi. rewrite KM by lf_err_side ERF i Hi. rewrite K2 by lf_err_side ERF i Hi.
  rewrite (HER2 i Hi). rewrite K1 by lf_err_side ERF i Hi. exact (HERR i Hi). }
assert (EB8 : ew Eb 8 = Z_to_bv 64 LA) by (rewrite OLDb, OLDa by lia; exact E8).
assert (EB18 : ew Eb 18 = Z_to_bv 64 SB) by (rewrite OLDb, OLDa by lia; exact E18).
assert (EB23 : ew Eb 23 = Z_to_bv 64 (Z.of_nat c)) by (rewrite OLDb, OLDa by lia; exact E23).
assert (EB32 : ew Eb 32 = Z_to_bv 64 (hl_v l)) by (rewrite OLDb, OLDa by lia; exact E32).
assert (EB33 : ew Eb 33 = Z_to_bv 64 (hl_cap l)) by (rewrite OLDb, OLDa by lia; exact E33).
destruct (lf_den_regs Eb LA EB8 EB18 ltac:(lia)) as (_ & D19 & D20 & D21).
psrr_branch_tok RUNG BRG HS SHOK3 lf_Bspan.
- (* c - 1 <> 0: back to the loop head *)
  lazymatch goal with Hb : branch_taken _ _ _ = true |- _ => rename Hb into Hbr end.
  rewrite branch_ne_U in Hbr.
  rewrite (U_atom_off Eb 23 (Z.of_nat c) (-1) EB23) in Hbr by lia.
  rewrite U_SLit, (zcanon_id 0) in Hbr by (unfold M64; lia).
  apply Bool.negb_true_iff, Z.eqb_neq in Hbr.
  assert (Hc0 : (c - 1 =? 0)%nat = false) by (apply Nat.eqb_neq; lia).
  rewrite Hc0 in HK.
  paj_run_to_tok_xR RUNTOG HS HJ3 SHOK3 lf_Bspan A_lf_loop.
  { lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
    apply awr_ok_x_cons_awr0; [awr_ok_tac; exact Uspb|]. apply awr_ok_x_cons_g; [|apply awr_ok_x_nil].
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]. rewrite U8b. intros a Ha. apply HLG. lia. }
  lazymatch goal with |- SRrG _ _ _ (mkCfg ?mm _) _ => rename mm into msf end.
  lazymatch goal with Hf : frame_of _ _ (mrestrict (w_H W2) (ms_mem ms3)) (mrestrict (w_H W2) (ms_mem msf)) |- _ => rename Hf into HFr4 end.
  lazymatch goal with Hgr : mem_grows (mrestrict (w_H W2) (ms_mem ms3)) (mrestrict (w_H W2) (ms_mem msf)) |- _ => rename Hgr into HGr4 end.
  lazymatch type of HFr4 with frame_of ?Ev ?rs _ _ => let rs' := eval vm_compute in rs in change rs with rs' in HFr4 end.
  assert (K4 : forall a, 0 <= a < 2 ^ 64 -> ~ (LA <= a < LA + 16) -> aview SEGS (w_H W2) (ms_mem msf) a = aview SEGS (w_H W2) (ms_mem ms3) a).
  { intros a Ha Hno. apply (aview_kept_out _ _ (w_H W2) (ms_mem ms3) (ms_mem msf) HFr4 a Ha).
    intros (rg & Hin & Hr). cbn [In] in Hin. destruct Hin as [<- | [<- | []]];
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr; [lia | rewrite U8b in Hr; lia]. }
  pmkst HS.
  prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4. prreg HS (8%bv : bv 5) F8.
  prreg HS (9%bv : bv 5) F9. prreg HS (18%bv : bv 5) F18. prreg HS (23%bv : bv 5) F23.
  prreg HS (25%bv : bv 5) F25. prreg HS (26%bv : bv 5) F26. prreg HS (27%bv : bv 5) F27.
  prreg_raw HS (19%bv : bv 5) F19. prreg_raw HS (20%bv : bv 5) F20. prreg_raw HS (21%bv : bv 5) F21.
  pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RS0.
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RL1.
  cbn [ms_mem restrict] in RS0, RL1.
  assert (VL0 : val_mem SEGS (mrestrict (w_H W2) (ms_mem msf)) (LA + 0) (N.to_nat 8) (hl_v l)).
  { eapply (field_of_region Eb _ 8 LA); [exact RL1 | exact U8b | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
    cbn [sv_denot]. rewrite EB32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
  assert (VL8 : val_mem SEGS (mrestrict (w_H W2) (ms_mem msf)) (LA + 8) (N.to_nat 4) (Z.of_nat (c - 1))).
  { eapply (field_of_region Eb _ 8 LA); [exact RL1 | exact U8b | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
    cbn [sv_denot]. rewrite EB23, unsigned_lit_small by lia. f_equal. lia. }
  assert (VL12 : val_mem SEGS (mrestrict (w_H W2) (ms_mem msf)) (LA + 12) (N.to_nat 4) (hl_cap l)).
  { eapply (field_of_region Eb _ 8 LA); [exact RL1 | exact U8b | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
    cbn [sv_denot]. rewrite EB33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
  rewrite Z.add_0_r in VL0.
  assert (HAWR : awr W2 (ms_mem msf) LA 16).
  { intros i Hi. destruct RL1 as (_ & _ & RLw & _). cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in RLw.
    rewrite U8b in RLw. exact (RLw i Hi). }
  assert (HVEC' : 0 < hl_cap l -> In (hl_v l, AREC * hl_cap l) (ablocks B ly2 S2) /\
    garr8 SEGS (arm W2 (ms_mem msf)) (hl_v l) (bzs (concat (map text_rec (hl_recs l)) ++ hl_junk l))).
  { intros _. split; [exact Hvin2|]. unfold arm in Hvg |- *.
    apply (lf_garr8_kept (w_H Wc) (w_H W2) memc (ms_mem msf)); [|exact Hvg].
    intros j Hj. rewrite Hvlen in Hj. rewrite K4 by (unfold alloc_ceiling in *; lia). apply VEC. lia. }
  eapply (HK W2 ly2 S2 Hp2 (ms_regs msf) (ms_mem msf) _ (kk + 1)).
  unfold lf_inv_xR.
  split; [exact HJ3|].
  split.
  { unfold lf_regs.
    split; [rewrite F2, OLDb, OLDa by lia; rewrite E2; exact R2|].
    split; [rewrite F3, OLDb, OLDa by lia; exact E3|].
    split; [rewrite F4, OLDb, OLDa by lia; exact E4|].
    split; [rewrite F8, OLDb, OLDa by lia; exact E8|].
    split; [rewrite F9, U8b; reflexivity|].
    split; [rewrite F18, OLDb, OLDa by lia; exact E18|].
    split; [rewrite F19; exact D19|].
    split; [rewrite F20; exact D20|].
    split; [rewrite F21; exact D21|].
    split; [rewrite F23, EB23, unsigned_lit_small by lia; f_equal; lia|].
    split; [rewrite F25, OLDb, OLDa by lia; exact E25|].
    split; [rewrite F26, OLDb, OLDa by lia; exact E26|].
    rewrite F27, OLDb, OLDa by lia; exact E27. }
  split.
  { intros i Hi. unfold arm.
    pose proof (bv_unsigned_in_range 64 (getr regs0 (Z_to_bv 5 (nth i lf_saved 0)))) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
    eapply (slot_of_region Eb _ (spZ regs0 - 80) _ 0 80 0 0 (8 * Z.of_nat i) (SOff (34 + i) 0)).
    - exact RS0.
    - exact Uspb.
    - clear - Hi. do 10 (destruct i as [|i]; [cbn [In]; repeat first [left; reflexivity | right] |]). lia.
    - cbn [sv_denot]. rewrite OLDb, OLDa by lia. rewrite (ESV i Hi), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    - exact Hr. }
  split; [exact VL0|]. split; [exact VL8|]. split; [exact VL12|]. split; [exact HAWR|]. split; [exact HVEC'|].
  split; [exact HTX2|]. split; [exact HPERM2|]. split; [exact HFRS2|]. split; [exact HML2'|].
  split; [intros a Hi Hno Herr Hpp; apply (lf_apresent_grows _ _ _ a HGr4); exact (PRS a Hi Hno Herr Hpp)|].
  split.
  { intros i Hi. rewrite K4 by lf_err_side ERF i Hi. exact (ERR3 i Hi). }
  split; [exact HRM2 | exact HCNT2].
- (* c - 1 = 0: out of the loop *)
  lazymatch goal with Hb : branch_taken _ _ _ = false |- _ => rename Hb into Hbr end.
  rewrite branch_ne_U in Hbr.
  rewrite (U_atom_off Eb 23 (Z.of_nat c) (-1) EB23) in Hbr by lia.
  rewrite U_SLit, (zcanon_id 0) in Hbr by (unfold M64; lia).
  apply Bool.negb_false_iff, Z.eqb_eq in Hbr.
  assert (Hc0 : (c - 1 =? 0)%nat = true) by (apply Nat.eqb_eq; lia).
  rewrite Hc0 in HK.
  paj_run_to_tok_xR RUNTOG HS HJ3 SHOK3 lf_Bspan A_lf_done.
  { lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
    apply awr_ok_x_cons_awr0; [awr_ok_tac; exact Uspb|]. apply awr_ok_x_cons_g; [|apply awr_ok_x_nil].
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]. rewrite U8b. intros a Ha. apply HLG. lia. }
  lazymatch goal with |- SRrG _ _ _ (mkCfg ?mm _) _ => rename mm into msf end.
  lazymatch goal with Hf : frame_of _ _ (mrestrict (w_H W2) (ms_mem ms3)) (mrestrict (w_H W2) (ms_mem msf)) |- _ => rename Hf into HFr4 end.
  lazymatch goal with Hgr : mem_grows (mrestrict (w_H W2) (ms_mem ms3)) (mrestrict (w_H W2) (ms_mem msf)) |- _ => rename Hgr into HGr4 end.
  lazymatch type of HFr4 with frame_of ?Ev ?rs _ _ => let rs' := eval vm_compute in rs in change rs with rs' in HFr4 end.
  assert (K4 : forall a, 0 <= a < 2 ^ 64 -> ~ (LA <= a < LA + 16) -> aview SEGS (w_H W2) (ms_mem msf) a = aview SEGS (w_H W2) (ms_mem ms3) a).
  { intros a Ha Hno. apply (aview_kept_out _ _ (w_H W2) (ms_mem ms3) (ms_mem msf) HFr4 a Ha).
    intros (rg & Hin & Hr). cbn [In] in Hin. destruct Hin as [<- | [<- | []]];
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr; [lia | rewrite U8b in Hr; lia]. }
  pmkst HS.
  prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4. prreg HS (8%bv : bv 5) F8.
  prreg HS (9%bv : bv 5) F9. prreg HS (18%bv : bv 5) F18. prreg HS (23%bv : bv 5) F23.
  prreg HS (25%bv : bv 5) F25. prreg HS (26%bv : bv 5) F26. prreg HS (27%bv : bv 5) F27.
  prreg_raw HS (19%bv : bv 5) F19. prreg_raw HS (20%bv : bv 5) F20. prreg_raw HS (21%bv : bv 5) F21.
  pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RS0.
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RL1.
  cbn [ms_mem restrict] in RS0, RL1.
  assert (VL0 : val_mem SEGS (mrestrict (w_H W2) (ms_mem msf)) (LA + 0) (N.to_nat 8) (hl_v l)).
  { eapply (field_of_region Eb _ 8 LA); [exact RL1 | exact U8b | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
    cbn [sv_denot]. rewrite EB32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
  assert (VL8 : val_mem SEGS (mrestrict (w_H W2) (ms_mem msf)) (LA + 8) (N.to_nat 4) (Z.of_nat (c - 1))).
  { eapply (field_of_region Eb _ 8 LA); [exact RL1 | exact U8b | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
    cbn [sv_denot]. rewrite EB23, unsigned_lit_small by lia. f_equal. lia. }
  assert (VL12 : val_mem SEGS (mrestrict (w_H W2) (ms_mem msf)) (LA + 12) (N.to_nat 4) (hl_cap l)).
  { eapply (field_of_region Eb _ 8 LA); [exact RL1 | exact U8b | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
    cbn [sv_denot]. rewrite EB33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
  rewrite Z.add_0_r in VL0.
  assert (HAWR : awr W2 (ms_mem msf) LA 16).
  { intros i Hi. destruct RL1 as (_ & _ & RLw & _). cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in RLw.
    rewrite U8b in RLw. exact (RLw i Hi). }
  assert (HVEC' : 0 < hl_cap l -> In (hl_v l, AREC * hl_cap l) (ablocks B ly2 S2) /\
    garr8 SEGS (arm W2 (ms_mem msf)) (hl_v l) (bzs (concat (map text_rec (hl_recs l)) ++ hl_junk l))).
  { intros _. split; [exact Hvin2|]. unfold arm in Hvg |- *.
    apply (lf_garr8_kept (w_H Wc) (w_H W2) memc (ms_mem msf)); [|exact Hvg].
    intros j Hj. rewrite Hvlen in Hj. rewrite K4 by (unfold alloc_ceiling in *; lia). apply VEC. lia. }
  eapply (HK W2 ly2 S2 Hp2 (ms_regs msf) (ms_mem msf) _ (kk + 1)).
  unfold lf_inv_xR.
  split; [exact HJ3|].
  split.
  { unfold lf_regs.
    split; [rewrite F2, OLDb, OLDa by lia; rewrite E2; exact R2|].
    split; [rewrite F3, OLDb, OLDa by lia; exact E3|].
    split; [rewrite F4, OLDb, OLDa by lia; exact E4|].
    split; [rewrite F8, OLDb, OLDa by lia; exact E8|].
    split; [rewrite F9, U8b; reflexivity|].
    split; [rewrite F18, OLDb, OLDa by lia; exact E18|].
    split; [rewrite F19; exact D19|].
    split; [rewrite F20; exact D20|].
    split; [rewrite F21; exact D21|].
    split; [rewrite F23, EB23, unsigned_lit_small by lia; f_equal; lia|].
    split; [rewrite F25, OLDb, OLDa by lia; exact E25|].
    split; [rewrite F26, OLDb, OLDa by lia; exact E26|].
    rewrite F27, OLDb, OLDa by lia; exact E27. }
  split.
  { intros i Hi. unfold arm.
    pose proof (bv_unsigned_in_range 64 (getr regs0 (Z_to_bv 5 (nth i lf_saved 0)))) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
    eapply (slot_of_region Eb _ (spZ regs0 - 80) _ 0 80 0 0 (8 * Z.of_nat i) (SOff (34 + i) 0)).
    - exact RS0.
    - exact Uspb.
    - clear - Hi. do 10 (destruct i as [|i]; [cbn [In]; repeat first [left; reflexivity | right] |]). lia.
    - cbn [sv_denot]. rewrite OLDb, OLDa by lia. rewrite (ESV i Hi), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    - exact Hr. }
  split; [exact VL0|]. split; [exact VL8|]. split; [exact VL12|]. split; [exact HAWR|]. split; [exact HVEC'|].
  split; [exact HTX2|]. split; [exact HPERM2|]. split; [exact HFRS2|]. split; [exact HML2'|].
  split; [intros a Hi Hno Herr Hpp; apply (lf_apresent_grows _ _ _ a HGr4); exact (PRS a Hi Hno Herr Hpp)|].
  split.
  { intros i Hi. rewrite K4 by lf_err_side ERF i Hi. exact (ERR3 i Hi). }
  split; [exact HRM2 | exact HCNT2].
Qed.
(* :1173 lf_exit_x *)
Lemma lf_exit_xR : forall W ly S Hp regs0 mem0 md0 ch LA (l : hlist) lines kr Wc lyc Sc Hpc regs memc mdc kk,
lf_ctx_x W ly S Hp regs0 mem0 md0 ch LA l lines ->
ajournal_gx_xR SEGS B PST ARx R G 0 [] LF_STK (spZ regs0) (blk_FP (list_blks l)) ly S Hp W mem0 md0 [] lyc Sc Hpc Wc memc mdc kk ->
lf_regsT regs regs0 LA -> lf_frame Wc memc (spZ regs0) regs0 ->
val_mem SEGS (arm Wc memc) LA 8 (hl_v l) -> val_mem SEGS (arm Wc memc) (LA + 8) 4 0 ->
val_mem SEGS (arm Wc memc) (LA + 12) 4 (hl_cap l) -> awr Wc memc LA 16 ->
(0 < hl_cap l -> In (hl_v l, AREC * hl_cap l) (ablocks B lyc Sc)) ->
(forall rest, Permutation (ablocks B ly S) (list_blks l ++ rest) -> Permutation (ablocks B lyc Sc) (lf_blks l 0 ++ rest)) ->
frames Sc = frames S -> mo_le MT S Sc (hl_n l * mo_free MT) -> apres_kept B W mem0 Wc memc ->
(forall i, 0 <= i < 4 -> aview SEGS (w_H Wc) memc (as_errno B + i) = aview SEGS (w_H W) mem0 (as_errno B + i)) ->
rp_RM RP Sc (1 + kr) -> cnt_ok RP (ablocks B lyc Sc) ->
SRrG SEGS R Wc (mkCfg (mkst regs (Z_to_bv 64 (BASE + A_lf_done)) memc (seg_rom SEGS)) mdc)
  (lf_post_xR B PST ARx R MT RP G regs0 ly S Hp W mem0 md0 LA l lines kr).
Proof.
intros W ly S Hp regs0 mem0 md0 ch LA l lines kr Wc lyc Sc Hpc regs memc mdc kk HCTX HJ HR Hfr Mv Mn Mc Hw HVEC HPERM HFRS HMLE HAPK HERR HRM HCNT.
destruct HCTX as (HPRE & HL & HLG & HZS & HROM & HMO).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof (lf_LA_range LA HLG) as (HLA1 & HLA2 & _ & _ & HLAe).
pose proof (lf_errno_facts (spZ regs0) LA ltac:(clear - Hceil Hslo; lia) HLG) as ERF.
pose proof HL as (_ & _ & _ & _ & (Hn0 & Hcap) & Hvc & Hnd & Hnv & HFA).
pose proof (ajournal_gx_AR_xR SEGS B PST ARx G 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARc.
assert (Hsp0 : lf_sp0 (spZ regs0)) by (split; [exact Hal16 | clear - Hceil Hslo Hshi H47; unfold LF_STK, ASTACK in *; lia]).
pose proof Hsp0 as (Hsp0a & Hsp0b & Hsp0c).
assert (Hv64 : 0 <= hl_v l < 2 ^ 48).
{ destruct Hvc as [[_ ->] | (Hcp & Hin & _)]; [lia|].
  destruct (alx_blocks _ _ _ LAWS ly S Hp W mem0 md0 _ _ HAR0 Hin) as (_ & H4096 & Hce & _).
  unfold req_size, AREC in Hce. destruct (Z.eqb_spec (16 * hl_cap l) 0); lia. }
destruct (lf_head_exit_x Wc lyc Sc Hpc memc mdc regs regs0 LA (hl_v l) (hl_cap l) HARc HR Hsp0 Hfr HLA1 HLA2 HZS Mv Mn Mc Hw
  ltac:(lia) ltac:(lia)) as [HS SHOK].
remember (Eimg (Ereg regs (lf_xl (hl_v l) (hl_cap l) 0 0 regs0))) as E eqn:HE in HS.
rewrite <- HE in SHOK.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
destruct HR as (R2 & R3 & R4 & R8 & R18 & R20 & R25 & R26 & R27).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs0 - 80) by (rewrite E2, R2; apply unsigned_lit_small; lia).
assert (E3 : ew E 3 = getr regs0 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 3 3%bv eq_refl); exact R3).
assert (E4 : ew E 4 = getr regs0 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 4 4%bv eq_refl); exact R4).
assert (E8 : ew E 8 = Z_to_bv 64 LA) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 8 8%bv eq_refl); exact R8).
assert (E18 : ew E 18 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact R18).
assert (E25 : ew E 25 = getr regs0 25) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact R25).
assert (E26 : ew E 26 = getr regs0 26) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact R26).
assert (E27 : ew E 27 = getr regs0 27) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact R27).
assert (E32 : ew E 32 = Z_to_bv 64 (hl_v l)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (ESV : forall i, (i < 10)%nat -> ew E (34 + i) = getr regs0 (Z_to_bv 5 (nth i lf_saved 0)))
by (intros i Hi; subst E; exact (lf_ew_saved regs regs0 _ _ _ _ i Hi)).
assert (U8 : bv_unsigned (ew E 8) = LA) by (rewrite E8; apply unsigned_lit_small; lia).
assert (HMOf : mo_ok MT Sc (mo_free MT)).
{ pose proof (mo_free_nonneg MT MLAW) as Hf.
  apply (mok_station MT S Sc (lf_cost MT l) (hl_n l * mo_free MT) (mo_free MT) MLAW HMO HMLE Hf).
  unfold lf_cost. nia. }
(* 0x86164 .. the jal to free *)
paj_run_tok_xR RUNG HS HJ SHOK lf_Bspan.
{ apply awr_ok_x_cons_awr0; [awr_ok_tac; exact Usp|]. apply awr_ok_x_cons_g; [|apply awr_ok_x_nil].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi lf_lregX lf_lreg base_val]. rewrite U8. intros a Ha. apply HLG. lia. }
lazymatch goal with |- SRrG _ _ _ (mkCfg ?mm _) _ => rename mm into ms end.
lazymatch goal with Hgr : mem_grows (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) (ms_mem ms)) |- _ =>
  assert (PR1 : forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) (ms_mem ms) a)
  by (intros a Hpp; exact (lf_apresent_grows (w_H Wc) memc (ms_mem ms) a Hgr Hpp)) end.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (LA <= a < LA + 16) -> aview SEGS (w_H Wc) (ms_mem ms) a = aview SEGS (w_H Wc) memc a).
{ intros a Ha Hno. lazymatch goal with Hf : frame_of _ _ (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) (ms_mem ms)) |- _ =>
    apply (aview_kept_out _ _ (w_H Wc) memc (ms_mem ms) Hf a Ha) end.
  intros (rg & Hin & Hr). cbn [ss_mem ss_lfX In] in Hin. destruct Hin as [<- | [<- | []]];
  cbn [lf_stackL lf_lregX lf_lreg YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr;
  [lia | rewrite U8 in Hr; lia]. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.
destruct HJ as (HSTK & HXO & (memS & HJi & Hag) & Hout). rewrite !Z.add_0_r in HJi.
pose proof (proj1 HJi) as HARm.
pose proof (RO_ARx _ _ _ _ _ _ HARm) as HROm.
assert (Usp2 : spZ (ms_regs ms) = spZ regs0 + -80) by (unfold spZ at 1; rewrite Q2, Usp; lia).
assert (R10s : getr (ms_regs ms) 10 = w64 (hl_v l)) by (rewrite Q10; exact E32).
assert (HGP : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite Q3, E3; exact Hgp).
assert (HTP : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite Q4, E4; exact Htp).
assert (HS0 : s0Z (ms_regs ms) = LA) by (unfold s0Z; rewrite Q8; exact U8).
assert (HCH : chain_pre lyc (aview SEGS (w_H Wc) (ms_mem ms)) (ms_regs ms) []).
{ unfold chain_pre. split; [unfold raZ; rewrite Q1; rewrite unsigned_lit_small by lia; lia|].
  destruct (frame0_ok lyc (ms_regs ms)); [|reflexivity].
  replace (bad_next (spZ (ms_regs ms)) (ly_top lyc) (s0Z (ms_regs ms))) with true; [reflexivity|].
  symmetry. unfold bad_next. rewrite HS0, Usp2. apply orb_true_iff. left. apply orb_true_iff. left. apply Z.leb_le. lia. }
(* the free's caller context: the chain is [] (s0 = LA, an image address), the trace the singleton [list_free + 0xf8] *)
assert (HCTXX : In (raZ (ms_regs ms) :: spine []) CTX).
{ cbn [spine map]. replace (raZ (ms_regs ms)) with (BASE + AF_fr_list_free + 0xf8); [exact HCTX_lf_exit|].
  unfold raZ. rewrite Q1, unsigned_lit_small by lia. first [lia | unfold AF_fr_list_free in *; lia]. }
rewrite HBfree.
(* free(v), or free(NULL) when cap = 0: the same bookkeeping either way *)
eapply (SRrG_bind SEGS R R_trans _ _ (fun W4 c4 => exists ly4 S4 Hp4 regs4 mem4 md4,
  c4 = mkCfg (mkst regs4 (getr (ms_regs ms) 1) mem4 (seg_rom SEGS)) md4 /\
  ajournal_xR SEGS B PST ARx R LF_STK (spZ regs0) (blk_FP (list_blks l)) ly S Hp W memS md0 [] ly4 S4 Hp4 W4 mem4 md4 (kk + 1) /\
  aregs_preserved (ms_regs ms) regs4 /\
  (forall rest, Permutation (ablocks B lyc Sc) (lf_blks l 0 ++ rest) -> Permutation (ablocks B ly4 S4) rest) /\
  frames S4 = frames Sc /\
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs0 + -80 - ASTACK <= a < spZ regs0 + -80) ->
   aview SEGS (w_H W4) mem4 a = aview SEGS (w_H Wc) (ms_mem ms) a) /\
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
   aview SEGS (w_H W4) mem4 a = aview SEGS (w_H Wc) (ms_mem ms) a) /\
  mo_le MT Sc S4 (mo_free MT) /\ rp_RM RP S4 kr /\
  (forall i, 0 <= i < 4 -> aview SEGS (w_H W4) mem4 (as_errno B + i) = aview SEGS (w_H Wc) (ms_mem ms) (as_errno B + i)) /\
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
   apresent (w_H Wc) (ms_mem ms) a -> apresent (w_H W4) mem4 a))).
{ destruct (Z.eq_dec (hl_cap l) 0) as [Hc0 | Hc0].
  - assert (Hv0 : hl_v l = 0) by (destruct Hvc as [[_ H] | (Hcp & _)]; [exact H | lia]).
    eapply (SRrG_mono SEGS R).
    { exact (AFREEN_R Wc (ms_regs ms) (ms_mem ms) LF_STK (spZ regs0) (blk_FP (list_blks l)) ly S Hp W memS md0 [] lyc Sc Hpc _ _
        (-80) (getr (ms_regs ms) 1) [] kr HJi ltac:(rewrite R10s, Hv0; reflexivity) Usp2 eq_refl ltac:(lia)
        ltac:(unfold LF_STK, ASTACK; lia)
        (aj_stack_room_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (-80) (ms_regs ms) HJi Usp2 ltac:(unfold LF_STK, ASTACK; lia))
        HGP HTP eq_refl ltac:(rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]) HCH HROm HCTXX HRM HCNT HMOf). }
    cbv beta. intros W4 c4 _ (ly4 & S4 & Hp4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & HPm & HFr4 & HK4 & HM4 & HRM4 & HE4 & HPr4).
    exists ly4, S4, Hp4, regs4, mem4, md4. split; [reflexivity|]. split; [exact HJ4|]. split; [exact HP4|].
    split.
    { intros rest Hpp. unfold lf_blks in Hpp. rewrite (proj2 (Z.eqb_eq _ _) Hc0) in Hpp. cbn [firstn map app] in Hpp.
      exact (Permutation_trans HPm Hpp). }
    split; [exact HFr4|].
    split; [exact (proj1 HK4)|].
    split; [exact (proj1 (proj2 (proj2 HK4)))|].
    split; [exact HM4|]. split; [exact HRM4|]. split; [exact HE4|].
    intros a Hi Ho He Hpp. pose proof (proj1 HJ4) as HAR4.
    apply (HPr4 a Hi); [intros Hao; apply Ho; exact (proj1 (alx_owned_image _ _ _ LAWS _ _ _ _ _ _ a HARm Hi) Hao)
      | intros Hao; apply Ho; exact (proj1 (alx_owned_image _ _ _ LAWS _ _ _ _ _ _ a HAR4 Hi) Hao) | exact He | exact Hpp].
  - assert (Hcp : 0 < hl_cap l) by lia.
    pose proof (HVEC Hcp) as Hvin.
    eapply (SRrG_mono SEGS R).
    { exact (AFREE_R Wc (ms_regs ms) (ms_mem ms) LF_STK (spZ regs0) (blk_FP (list_blks l)) ly S Hp W memS md0 [] lyc Sc Hpc _ _
        (hl_v l) (AREC * hl_cap l) (-80) (getr (ms_regs ms) 1) [] kr HJi Hvin R10s Usp2 eq_refl ltac:(lia)
        ltac:(unfold LF_STK, ASTACK; lia)
        (aj_stack_room_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (-80) (ms_regs ms) HJi Usp2 ltac:(unfold LF_STK, ASTACK; lia))
        HGP HTP eq_refl ltac:(rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]) HCH HROm HCTXX HRM HCNT
        ltac:(intros _ i Hi; apply (inFP_ablocks_fp (list_blks l) (hl_v l) (AREC * hl_cap l) i);
              [unfold list_blks; rewrite (proj2 (Z.eqb_neq _ _) Hc0); apply in_or_app; left; left; reflexivity | exact Hi]) HMOf). }
    cbv beta. intros W4 c4 _ (ly4 & S4 & Hp4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & (l1 & l2 & Eb1 & Eb2) & HFr4 & HK4 & HM4 & HRM4 & HE4 & HPr4).
    exists ly4, S4, Hp4, regs4, mem4, md4. split; [reflexivity|]. split; [exact HJ4|]. split; [exact HP4|].
    split.
    { intros rest Hpp. rewrite Eb2. rewrite Eb1 in Hpp. unfold lf_blks in Hpp. rewrite (proj2 (Z.eqb_neq _ _) Hc0) in Hpp.
      cbn [firstn map app] in Hpp. apply Permutation_sym in Hpp. apply Permutation_cons_app_inv in Hpp. exact (Permutation_sym Hpp). }
    split; [exact HFr4|].
    split; [exact (proj1 HK4)|].
    split; [exact (proj1 (proj2 (proj2 HK4)))|].
    split; [exact HM4|]. split; [exact HRM4|]. split; [exact HE4|].
    intros a Hi Ho He Hpp. pose proof (proj1 HJ4) as HAR4.
    apply (HPr4 a Hi); [intros Hao; apply Ho; exact (proj1 (alx_owned_image _ _ _ LAWS _ _ _ _ _ _ a HARm Hi) Hao)
      | intros Hao; apply Ho; exact (proj1 (alx_owned_image _ _ _ LAWS _ _ _ _ _ _ a HAR4 Hi) Hao) | exact He | | exact Hpp].
    intros Hb. exact (blk_img_x SEGS B ARx LAWS lyc Sc Hpc Wc (ms_mem ms) _ _ _ a HARm Hvin Hb Hi). }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & Hp4 & regs4 & mem4 & md4 & -> & HJi4 & HP4 & HPM4 & HFR4 & KS4 & KI4 & HML4 & HRM4 & HER4 & HPR4).
rewrite Q1.
pose proof (proj1 HJi4) as HAR4.
assert (HJ4 : ajournal_gx_xR SEGS B PST ARx R G 0 [] LF_STK (spZ regs0) (blk_FP (list_blks l)) ly S Hp W mem0 md0 [] ly4 S4 Hp4 W4 mem4 md4 (kk + 1)).
{ apply (ajournal_gx_pack_xR SEGS B PST ARx G 0 [] LF_STK (spZ regs0) _ ly S Hp W mem0 md0 [] ly4 S4 Hp4 W4 mem4 md4 (kk + 1) memS HSTK HXO);
  [rewrite !Z.add_0_r; exact HJi4 | exact Hag | apply out_none]. }
(* ---- keep the frame and the list struct across the call ---- *)
assert (HLAimg : forall a, LA <= a < LA + 16 ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4))
by (intros a Ha; exact (conj (proj1 (HG a (HLG a Ha))) (conj (proj1 (proj2 (HG a (HLG a Ha)))) (proj1 (HGR a (HLG a Ha)))))).
jafter_call_keep_pi HS 46%nat regs4 (mrestrict (w_H W4) mem4) HP4 [0; 1]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - apply (lf_region_kept2 E Wc W4 (ms_mem ms) mem4 2 (spZ regs0 - 80)); [exact Usp | | intros a Ha; exfalso; lia].
    intros a Ha. apply KS4; [lia | lia].
  - apply (lf_region_kept2 E Wc W4 (ms_mem ms) mem4 8 LA); [exact U8 | |].
    + intros a Ha. destruct (HLAimg a ltac:(lia)) as (Hi & Ho & He). exact (KI4 a Hi Ho He).
    + intros a Ha. destruct (HLAimg a ltac:(lia)) as (Hi & Ho & He).
      apply (lf_writable_img Wc W4 (ms_mem ms) mem4 a Hi). exact (HPR4 a Hi Ho He). }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 46 (map (getr regs4) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 46)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
clear HEa.
assert (SHOK2 : sh_ok SEGS lf_BxL lf_SHT Ea (mrestrict (w_H W4) mem4)).
{ unfold sh_ok, lf_SHT. constructor; [|constructor].
  apply (lf_shent8_x Ea ly4 S4 Hp4 W4 mem4 md4 LA HAR4 HZS); [rewrite OLDa by lia; exact E8 | rewrite OLDa by lia; exact E18 | exact HLA1 | exact HLA2]. }
assert (Uspa : bv_unsigned (ew Ea 2) = spZ regs0 - 80) by (rewrite OLDa by lia; exact Usp).
assert (U8a : bv_unsigned (ew Ea 8) = LA) by (rewrite OLDa by lia; exact U8).
(* 0x86178 .. the ret: v = 0, cap = 0, the epilogue *)
paj_run_tok_xR RUNG HS HJ4 SHOK2 lf_Bspan.
{ apply awr_ok_x_cons_awr0; [awr_ok_tac; exact Uspa|]. apply awr_ok_x_cons_g; [|apply awr_ok_x_nil].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]. rewrite U8a. intros a Ha. apply HLG. lia. }
lazymatch goal with |- SRrG _ _ _ (mkCfg ?mm _) _ => rename mm into msf end.
lazymatch goal with Hgr : mem_grows (mrestrict (w_H W4) mem4) (mrestrict (w_H W4) (ms_mem msf)) |- _ => rename Hgr into HGrf end.
lazymatch goal with Hf : frame_of _ _ (mrestrict (w_H W4) mem4) (mrestrict (w_H W4) (ms_mem msf)) |- _ => rename Hf into HFrf end.
assert (Kf : forall a, 0 <= a < 2 ^ 64 -> ~ (LA <= a < LA + 16) -> aview SEGS (w_H W4) (ms_mem msf) a = aview SEGS (w_H W4) mem4 a).
{ intros a Ha Hno. apply (aview_kept_out _ _ (w_H W4) mem4 (ms_mem msf) HFrf a Ha).
  intros (rg & Hin & Hr). cbn [In] in Hin. destruct Hin as [<- | [<- | []]];
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr; [lia | rewrite U8a in Hr; lia]. }
prreg HS (1%bv : bv 5) F1. prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4.
prreg HS (8%bv : bv 5) F8. prreg HS (9%bv : bv 5) F9. prreg HS (18%bv : bv 5) F18. prreg HS (19%bv : bv 5) F19.
prreg HS (20%bv : bv 5) F20. prreg HS (21%bv : bv 5) F21. prreg HS (22%bv : bv 5) F22. prreg HS (23%bv : bv 5) F23.
prreg HS (24%bv : bv 5) F24. prreg HS (25%bv : bv 5) F25. prreg HS (26%bv : bv 5) F26. prreg HS (27%bv : bv 5) F27.
assert (HPF : aregs_preserved regs0 (ms_regs msf)).
{ apply aregs_preserved_eqs.
  - rewrite F2, Uspa. replace (spZ regs0 - 80 + 80) with (spZ regs0) by lia. unfold spZ. apply Z_to_bv_bv_unsigned.
  - rewrite F3, OLDa by lia. exact E3.
  - rewrite F4, OLDa by lia. exact E4.
  - rewrite F8, OLDa by lia. exact (ESV 8%nat ltac:(lia)).
  - rewrite F9, OLDa by lia. exact (ESV 7%nat ltac:(lia)).
  - rewrite F18, OLDa by lia. exact (ESV 6%nat ltac:(lia)).
  - rewrite F19, OLDa by lia. exact (ESV 5%nat ltac:(lia)).
  - rewrite F20, OLDa by lia. exact (ESV 4%nat ltac:(lia)).
  - rewrite F21, OLDa by lia. exact (ESV 3%nat ltac:(lia)).
  - rewrite F22, OLDa by lia. exact (ESV 2%nat ltac:(lia)).
  - rewrite F23, OLDa by lia. exact (ESV 1%nat ltac:(lia)).
  - rewrite F24, OLDa by lia. exact (ESV 0%nat ltac:(lia)).
  - rewrite F25, OLDa by lia. exact E25.
  - rewrite F26, OLDa by lia. exact E26.
  - rewrite F27, OLDa by lia. exact E27. }
assert (ER1 : ew E 43 = getr regs0 1) by exact (ESV 9%nat ltac:(lia)).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ => set (Ef := Ev) in HS end.
assert (UF : forall m, (m < 512)%nat -> ew Ef m = ew Ea m) by (intros m Hm; subst Ef; rewrite ?ew_ewset_other by lia; reflexivity).
assert (U8f : bv_unsigned (ew Ef 8) = LA) by (rewrite UF by lia; exact U8a).
pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RL1. cbn [ms_mem restrict] in RL1.
assert (VL0 : val_mem SEGS (mrestrict (w_H W4) (ms_mem msf)) (LA + 0) (N.to_nat 8) 0).
{ eapply (field_of_region Ef _ 8 LA); [exact RL1 | exact U8f | cbn [In]; repeat first [left; reflexivity | right] | reflexivity | zside | zside]. }
assert (VL8 : val_mem SEGS (mrestrict (w_H W4) (ms_mem msf)) (LA + 8) (N.to_nat 4) 0).
{ eapply (field_of_region Ef _ 8 LA); [exact RL1 | exact U8f | cbn [In]; repeat first [left; reflexivity | right] | reflexivity | zside | zside]. }
assert (VL12 : val_mem SEGS (mrestrict (w_H W4) (ms_mem msf)) (LA + 12) (N.to_nat 4) 0).
{ eapply (field_of_region Ef _ 8 LA); [exact RL1 | exact U8f | cbn [In]; repeat first [left; reflexivity | right] | reflexivity | zside | zside]. }
rewrite Z.add_0_r in VL0.
assert (HAWR : awr W4 (ms_mem msf) LA 16).
{ intros i Hi. destruct RL1 as (_ & _ & RLw & _). cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in RLw.
  rewrite U8f in RLw. exact (RLw i Hi). }
apply (SRr_SRrG SEGS R WLE_R).
eapply (RET W4 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros matf. unfold lf_post_xR.
exists ly4, S4, Hp4, (ms_regs msf), (ms_mem msf). eexists. exists (kk + 1).
split; [rewrite F1, OLDa by lia; rewrite ER1, Hra; reflexivity|].
split; [apply (ajournal_gx_materialize_xR SEGS B PST ARx LAWS Hsegs); exact HJ4|].
split; [exact HPF|].
split.
{ unfold alist_at, empty_list, hl_n. cbn [hl_v hl_cap hl_recs hl_junk length Z.of_nat].
  split; [exact VL0|]. split; [exact VL8|]. split; [exact VL12|]. split; [exact HAWR|].
  split; [lia|]. split; [left; split; reflexivity|]. split; [constructor|]. split; [intros []|]. constructor. }
split; [intros rest Hpp; exact (HPM4 rest (HPERM rest Hpp))|].
split.
{ intros a Hi Hno Herr Hpp. apply (lf_apresent_grows _ _ _ a HGrf). apply (HPR4 a Hi Hno Herr). apply PR1.
  exact (HAPK a Hi Hno Herr Hpp). }
split.
{ intros i Hi. rewrite Kf by lf_err_side ERF i Hi. rewrite (HER4 i Hi). rewrite K1 by lf_err_side ERF i Hi. exact (HERR i Hi). }
split; [rewrite HFR4; exact HFRS|].
split; [|exact HRM4].
replace (lf_cost MT l) with (hl_n l * mo_free MT + mo_free MT) by (unfold lf_cost; ring).
exact (mle_station MT S Sc S4 _ _ MLAW HMLE HML4).
Qed.
(* :1415 lf_exit_inv_x *)
Lemma lf_exit_inv_xR : forall W ly S Hp regs0 mem0 md0 ch LA (l : hlist) lines kr Wc lyc Sc Hpc regs memc mdc kk,
lf_ctx_x W ly S Hp regs0 mem0 md0 ch LA l lines -> lf_inv_xR W ly S Hp regs0 mem0 md0 LA l 0 kr Wc lyc Sc Hpc regs memc mdc kk ->
SRrG SEGS R Wc (mkCfg (mkst regs (Z_to_bv 64 (BASE + A_lf_done)) memc (seg_rom SEGS)) mdc)
  (lf_post_xR B PST ARx R MT RP G regs0 ly S Hp W mem0 md0 LA l lines kr).
Proof.
intros W ly S Hp regs0 mem0 md0 ch LA l lines kr Wc lyc Sc Hpc regs memc mdc kk HCTX
  (HJ & HR & Hfr & Mv & Mn & Mc & Hw & HVEC & _ & HPERM & HFRS & HMLE & HAPK & HERR & HRM & HCNT).
destruct HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R21 & R23 & R25 & R26 & R27).
apply (lf_exit_xR W ly S Hp regs0 mem0 md0 ch LA l lines kr Wc lyc Sc Hpc regs memc mdc kk HCTX HJ).
- unfold lf_regsT. repeat (split; [assumption|]). assumption.
- exact Hfr.
- exact Mv.
- exact Mn.
- exact Mc.
- exact Hw.
- intros Hc. exact (proj1 (HVEC Hc)).
- exact HPERM.
- exact HFRS.
- replace (hl_n l * mo_free MT) with ((hl_n l - Z.of_nat 0) * mo_free MT) by (cbn [Z.of_nat]; ring). exact HMLE.
- exact HAPK.
- exact HERR.
- exact HRM.
- exact HCNT.
Qed.
(* :1440 pb_list_free_x *)
Theorem pb_list_free_xR : lf_spec_xR B PST ARx R MT RP G A_list_freeP.
Proof.
intros W ly S Hp regs mem md ch LA l lines HPRE H10 HAL8 HL HLG HZS HROM HMO kr HRM0 HCNT0.
assert (HCTX : lf_ctx_x W ly S Hp regs mem md ch LA l lines) by (exact (conj HPRE (conj HL (conj HLG (conj HZS (conj HROM HMO)))))).
(* the loop, by induction on the texts left *)
assert (IND : forall c Wc lyc Sc Hpc regsc memc mdc kc, (c <= length (hl_recs l))%nat ->
  lf_inv_xR W ly S Hp regs mem md LA l c kr Wc lyc Sc Hpc regsc memc mdc kc ->
  SRrG SEGS R Wc (mkCfg (mkst regsc (Z_to_bv 64 (BASE + if (c =? 0)%nat then A_lf_done else A_lf_loop)) memc (seg_rom SEGS)) mdc)
    (lf_post_xR B PST ARx R MT RP G regs ly S Hp W mem md LA l lines kr)).
{ induction c as [|c IH]; intros Wc lyc Sc Hpc regsc memc mdc kc Hcl HI; cbn [Nat.eqb].
  - exact (lf_exit_inv_xR W ly S Hp regs mem md ch LA l lines kr Wc lyc Sc Hpc regsc memc mdc kc HCTX HI).
  - apply (lf_iter_xR (Datatypes.S c) W ly S Hp regs mem md ch LA l lines kr Wc lyc Sc Hpc regsc memc mdc kc HCTX ltac:(lia) HI).
    intros Wc' lyc' Sc' Hpc' regs' memc' mdc' kk' HI'.
    replace (Datatypes.S c - 1)%nat with c in * by lia. exact (IH Wc' lyc' Sc' Hpc' regs' memc' mdc' kk' ltac:(lia) HI'). }
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct (lf_entry_x W ly S Hp regs mem md ch LA l lines HPRE H10 HL HLG HZS) as [HS SHOK].
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof HL as (Mv & Mn & Mc & Hw & (Hn0 & Hcap) & Hvc & Hnd & Hnv & HFA).
pose proof (ajournal_gx_init_xR SEGS B PST ARx R_refl G 0 [] LF_STK (blk_FP (list_blks l)) ly S Hp W regs mem md ch HPRE
  ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(intros a Ha; lia)) as HJ.
remember (Eimg (Ereg regs (lf_extra l))) as E eqn:HE in HS.
rewrite <- HE in SHOK.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E25 : ew E 25 = getr regs 25) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 25 25%bv eq_refl)).
assert (E26 : ew E 26 = getr regs 26) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 26 26%bv eq_refl)).
assert (E27 : ew E 27 = getr regs 27) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 27 27%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 LA) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 (hl_v l)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (hl_n l)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (hl_cap l)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (ERS : forall i, (i < 10)%nat -> ew E (Z.to_nat (nth i lf_saved 0)) = getr regs (Z_to_bv 5 (nth i lf_saved 0)))
by (intros i Hi; subst E; exact (lf_ew_regs regs _ i Hi)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
pose proof (lf_LA_range LA HLG) as (HLA1 & HLA2 & _).
pose proof (lf_errno_facts (spZ regs) LA ltac:(clear - Hceil Hslo; lia) HLG) as ERF.
assert (U10 : bv_unsigned (ew E 10) = LA) by (rewrite E10; apply unsigned_lit_small; lia).
assert (HnZ : 0 <= hl_n l) by (unfold hl_n; lia).
assert (Hv64 : 0 <= hl_v l < 2 ^ 48).
{ destruct Hvc as [[_ ->] | (Hcp & Hin & _)]; [lia|].
  destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hin) as (_ & H4096 & Hce & _).
  unfold req_size, AREC in Hce. destruct (Z.eqb_spec (16 * hl_cap l) 0); lia. }
destruct (lf_den_regs E LA E10 E35 ltac:(lia)) as (D9 & D19 & D20 & D21).
unfold cfg_at. change (w64 A_list_freeP) with (Z_to_bv 64 A_list_freeP).
unfold A_list_freeP, A_list_free.
(* the prologue, to the test of n *)
paj_run_tok_xR RUNG HS HJ SHOK lf_Bspan.
{ apply awr_ok_x_cons_awr0; [awr_ok_tac; exact Usp|]. apply awr_ok_x_cons_awr0; [awr_ok_tac|].
  apply awr_ok_x_cons_awr0; [awr_ok_tac|]. apply awr_ok_x_cons_g; [|apply awr_ok_x_nil].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi lf_lreg base_val]. rewrite U10.
  intros a Ha. apply HLG. lia. }
lazymatch goal with |- SRrG _ _ _ (mkCfg ?mm _) _ => rename mm into ms0 end.
lazymatch goal with Hf : frame_of _ _ (mrestrict (w_H W) mem) (mrestrict (w_H W) (ms_mem ms0)) |- _ => rename Hf into HFr0 end.
lazymatch goal with Hgr : mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) (ms_mem ms0)) |- _ => rename Hgr into HGr0 end.
assert (K0 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 80 <= a < spZ regs) -> ~ (LA <= a < LA + 16) ->
  aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a).
{ intros a Ha H1 H2. apply (aview_kept_out _ _ (w_H W) mem (ms_mem ms0) HFr0 a Ha).
  intros (rg & Hin & Hr). cbn [ss_mem ss_lf0 lf_regions0 In] in Hin. destruct Hin as [<- | [<- | [<- | [<- | []]]]];
  cbn [stack_region got_regionP bcell_regionP lf_lreg LF_FRAME YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr;
  [rewrite Usp in Hr; unfold LF_FRAME in Hr; lia | lia | lia | rewrite U10 in Hr; lia]. }
psrr_branch_tok RUNG BRG HS SHOK lf_Bspan.
- (* n = 0: straight to the exit *)
  lazymatch goal with Hb : branch_taken _ _ _ = true |- _ => rename Hb into Hbr end.
  rewrite branch_eq_U in Hbr. rewrite (U_atom E 33 (hl_n l) E33) in Hbr by lia.
  rewrite U_SLit, (zcanon_id 0) in Hbr by (unfold M64; lia).
  apply Z.eqb_eq in Hbr.
  assert (Hrn : hl_recs l = []) by (unfold hl_n in Hbr; destruct (hl_recs l); [reflexivity | cbn [length] in Hbr; lia]).
  paj_run_to_tok_xR RUNTOG HS HJ SHOK lf_Bspan A_lf_done.
  { lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
    apply awr_ok_x_cons_awr0; [awr_ok_tac; exact Usp|]. apply awr_ok_x_cons_awr0; [awr_ok_tac|].
    apply awr_ok_x_cons_awr0; [awr_ok_tac|]. apply awr_ok_x_cons_g; [|apply awr_ok_x_nil].
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]. rewrite U10. intros a Ha. apply HLG. lia. }
  lazymatch goal with |- SRrG _ _ _ (mkCfg ?mm _) _ => rename mm into msf end.
  lazymatch goal with Hgr : mem_grows (mrestrict (w_H W) (ms_mem ms0)) (mrestrict (w_H W) (ms_mem msf)) |- _ => rename Hgr into HGrf end.
  lazymatch goal with Hf : frame_of _ _ (mrestrict (w_H W) (ms_mem ms0)) (mrestrict (w_H W) (ms_mem msf)) |- _ => rename Hf into HFrf end.
  lazymatch type of HFrf with frame_of ?Ev ?rs _ _ => let rs' := eval vm_compute in rs in change rs with rs' in HFrf end.
  assert (K5 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 80 <= a < spZ regs) -> ~ (LA <= a < LA + 16) ->
    aview SEGS (w_H W) (ms_mem msf) a = aview SEGS (w_H W) (ms_mem ms0) a).
  { intros a Ha H1 H2. apply (aview_kept_out _ _ (w_H W) (ms_mem ms0) (ms_mem msf) HFrf a Ha).
    intros (rg & Hin & Hr). cbn [In] in Hin. destruct Hin as [<- | [<- | [<- | [<- | []]]]];
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr;
    [rewrite Usp in Hr; lia | lia | lia | rewrite U10 in Hr; lia]. }
  pmkst HS.
  prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4. prreg HS (8%bv : bv 5) F8.
  prreg HS (18%bv : bv 5) F18. prreg HS (25%bv : bv 5) F25. prreg HS (26%bv : bv 5) F26. prreg HS (27%bv : bv 5) F27.
  prreg_raw HS (20%bv : bv 5) F20.
  pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RS0.
  pose proof (st_ok_pi_region_nth _ _ _ 3 _ HS eq_refl) as RL3.
  cbn [ms_mem restrict] in RS0, RL3.
  assert (FRM0 : lf_frame W (ms_mem msf) (spZ regs) regs).
  { intros i Hi. unfold arm.
    pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 (nth i lf_saved 0)))) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
    replace (spZ regs - 80 + 8 * Z.of_nat i) with (spZ regs + (-80 + 8 * Z.of_nat i)) by ring.
    eapply (slot_of_region E _ (spZ regs) _ (-80) 0 (-80) 0 (-80 + 8 * Z.of_nat i) (SOff (Z.to_nat (nth i lf_saved 0)) 0)).
    - exact RS0.
    - exact Usp.
    - clear - Hi. do 10 (destruct i as [|i]; [cbn [In]; repeat first [left; reflexivity | right] |]). lia.
    - cbn [sv_denot]. rewrite (ERS i Hi), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    - exact Hr. }
  assert (VL0 : val_mem SEGS (mrestrict (w_H W) (ms_mem msf)) (LA + 0) (N.to_nat 8) (hl_v l)).
  { eapply (field_of_region E _ 10 LA); [exact RL3 | exact U10 | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
    cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
  assert (VL8 : val_mem SEGS (mrestrict (w_H W) (ms_mem msf)) (LA + 8) (N.to_nat 4) (hl_n l)).
  { eapply (field_of_region E _ 10 LA); [exact RL3 | exact U10 | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
    cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
  assert (VL12 : val_mem SEGS (mrestrict (w_H W) (ms_mem msf)) (LA + 12) (N.to_nat 4) (hl_cap l)).
  { eapply (field_of_region E _ 10 LA); [exact RL3 | exact U10 | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
    cbn [sv_denot]. rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
  rewrite Z.add_0_r in VL0. rewrite Hbr in VL8.
  assert (HAWR : awr W (ms_mem msf) LA 16).
  { intros i Hi. destruct RL3 as (_ & _ & RLw & _). cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in RLw.
    rewrite U10 in RLw. exact (RLw i Hi). }
  eapply (lf_exit_xR W ly S Hp regs mem md ch LA l lines kr W ly S Hp (ms_regs msf) (ms_mem msf) _ 0 HCTX HJ).
  + unfold lf_regsT.
    split; [rewrite F2, Usp; f_equal; lia|].
    split; [rewrite F3, E3; reflexivity|].
    split; [rewrite F4, E4; reflexivity|].
    split; [rewrite F8, E10; reflexivity|].
    split; [rewrite F18, E35; reflexivity|].
    split; [rewrite F20; exact D20|].
    split; [rewrite F25, E25; reflexivity|].
    split; [rewrite F26, E26; reflexivity|].
    rewrite F27, E27; reflexivity.
  + exact FRM0.
  + exact VL0.
  + exact VL8.
  + exact VL12.
  + exact HAWR.
  + intros Hcp. destruct Hvc as [[H0 _] | (_ & Hin & _)]; [lia | exact Hin].
  + intros rest Hpp. unfold lf_blks, list_blks in *. rewrite Hrn in Hpp. cbn [firstn map] in Hpp |- *. exact Hpp.
  + reflexivity.
  + rewrite Hbr, Z.mul_0_l. exact (mle_start MT S MLAW).
  + intros a Hi Hno Herr Hpp. apply (lf_apresent_grows _ _ _ a HGrf). exact (lf_apresent_grows _ _ _ a HGr0 Hpp).
  + intros i Hi. rewrite K5 by lf_err_side ERF i Hi. apply K0; lf_err_side ERF i Hi.
  + eapply (lf_rm_cast RP S _ _ HRM0). rewrite lf_rk, Hrn. reflexivity.
  + exact HCNT0.
- (* n > 0: into the loop *)
  lazymatch goal with Hb : branch_taken _ _ _ = false |- _ => rename Hb into Hbr end.
  rewrite branch_eq_U in Hbr. rewrite (U_atom E 33 (hl_n l) E33) in Hbr by lia.
  rewrite U_SLit, (zcanon_id 0) in Hbr by (unfold M64; lia).
  apply Z.eqb_neq in Hbr.
  assert (Hn0' : (length (hl_recs l) =? 0)%nat = false) by (apply Nat.eqb_neq; unfold hl_n in Hbr; lia).
  paj_run_to_tok_xR RUNTOG HS HJ SHOK lf_Bspan A_lf_loop.
  { lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
    apply awr_ok_x_cons_awr0; [awr_ok_tac; exact Usp|]. apply awr_ok_x_cons_awr0; [awr_ok_tac|].
    apply awr_ok_x_cons_awr0; [awr_ok_tac|]. apply awr_ok_x_cons_g; [|apply awr_ok_x_nil].
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]. rewrite U10. intros a Ha. apply HLG. lia. }
  lazymatch goal with |- SRrG _ _ _ (mkCfg ?mm _) _ => rename mm into msf end.
  lazymatch goal with Hgr : mem_grows (mrestrict (w_H W) (ms_mem ms0)) (mrestrict (w_H W) (ms_mem msf)) |- _ => rename Hgr into HGrf end.
  lazymatch goal with Hf : frame_of _ _ (mrestrict (w_H W) (ms_mem ms0)) (mrestrict (w_H W) (ms_mem msf)) |- _ => rename Hf into HFrf end.
  lazymatch type of HFrf with frame_of ?Ev ?rs _ _ => let rs' := eval vm_compute in rs in change rs with rs' in HFrf end.
  assert (K5 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 80 <= a < spZ regs) -> ~ (LA <= a < LA + 16) ->
    aview SEGS (w_H W) (ms_mem msf) a = aview SEGS (w_H W) (ms_mem ms0) a).
  { intros a Ha H1 H2. apply (aview_kept_out _ _ (w_H W) (ms_mem ms0) (ms_mem msf) HFrf a Ha).
    intros (rg & Hin & Hr). cbn [In] in Hin. destruct Hin as [<- | [<- | [<- | [<- | []]]]];
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr;
    [rewrite Usp in Hr; lia | lia | lia | rewrite U10 in Hr; lia]. }
  pmkst HS.
  prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4. prreg HS (8%bv : bv 5) F8.
  prreg HS (9%bv : bv 5) F9. prreg HS (18%bv : bv 5) F18. prreg HS (23%bv : bv 5) F23.
  prreg HS (25%bv : bv 5) F25. prreg HS (26%bv : bv 5) F26. prreg HS (27%bv : bv 5) F27.
  prreg_raw HS (19%bv : bv 5) F19. prreg_raw HS (20%bv : bv 5) F20. prreg_raw HS (21%bv : bv 5) F21.
  pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RS0.
  pose proof (st_ok_pi_region_nth _ _ _ 3 _ HS eq_refl) as RL3.
  cbn [ms_mem restrict] in RS0, RL3.
  assert (FRM0 : lf_frame W (ms_mem msf) (spZ regs) regs).
  { intros i Hi. unfold arm.
    pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 (nth i lf_saved 0)))) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
    replace (spZ regs - 80 + 8 * Z.of_nat i) with (spZ regs + (-80 + 8 * Z.of_nat i)) by ring.
    eapply (slot_of_region E _ (spZ regs) _ (-80) 0 (-80) 0 (-80 + 8 * Z.of_nat i) (SOff (Z.to_nat (nth i lf_saved 0)) 0)).
    - exact RS0.
    - exact Usp.
    - clear - Hi. do 10 (destruct i as [|i]; [cbn [In]; repeat first [left; reflexivity | right] |]). lia.
    - cbn [sv_denot]. rewrite (ERS i Hi), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    - exact Hr. }
  assert (VL0 : val_mem SEGS (mrestrict (w_H W) (ms_mem msf)) (LA + 0) (N.to_nat 8) (hl_v l)).
  { eapply (field_of_region E _ 10 LA); [exact RL3 | exact U10 | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
    cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
  assert (VL8 : val_mem SEGS (mrestrict (w_H W) (ms_mem msf)) (LA + 8) (N.to_nat 4) (hl_n l)).
  { eapply (field_of_region E _ 10 LA); [exact RL3 | exact U10 | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
    cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
  assert (VL12 : val_mem SEGS (mrestrict (w_H W) (ms_mem msf)) (LA + 12) (N.to_nat 4) (hl_cap l)).
  { eapply (field_of_region E _ 10 LA); [exact RL3 | exact U10 | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
    cbn [sv_denot]. rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
  rewrite Z.add_0_r in VL0.
  assert (HAWR : awr W (ms_mem msf) LA 16).
  { intros i Hi. destruct RL3 as (_ & _ & RLw & _). cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in RLw.
    rewrite U10 in RLw. exact (RLw i Hi). }
  assert (HVEC : 0 < hl_cap l -> In (hl_v l, AREC * hl_cap l) (ablocks B ly S) /\
    garr8 SEGS (arm W (ms_mem msf)) (hl_v l) (bzs (concat (map text_rec (hl_recs l)) ++ hl_junk l))).
  { intros Hcp. destruct Hvc as [[H0 _] | (_ & Hin & Hjl & Hg)]; [lia|]. split; [exact Hin|].
    destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hin) as (_ & H4096 & Hce & _).
    pose proof (blk_off_imgP_x B ARx LAWS IMGC BLKN _ _ _ _ _ _ _ _ HAR Hin) as Hoff.
    assert (Rq : req_size (AREC * hl_cap l) = 16 * hl_cap l) by (unfold req_size, AREC; destruct (Z.eqb_spec (16 * hl_cap l) 0); lia).
    rewrite Rq in Hce, Hoff. unfold off_img in Hoff.
    assert (Hvlen : Z.of_nat (length (bzs (concat (map text_rec (hl_recs l)) ++ hl_junk l))) = 16 * hl_cap l).
    { unfold bzs. rewrite length_map, length_app, lf_len_text_recs. unfold hl_n, AREC in *. lia. }
    unfold arm in Hg |- *. apply (lf_garr8_kept (w_H W) (w_H W) mem (ms_mem msf)); [|exact Hg].
    intros j Hj. rewrite Hvlen in Hj.
    rewrite K5 by (unfold LF_STK, ASTACK in *; lia). apply K0; unfold LF_STK, ASTACK in *; lia. }
  lazymatch goal with |- SRrG _ _ _ (mkCfg _ ?mdf) _ =>
    assert (HINV : lf_inv_xR W ly S Hp regs mem md LA l (length (hl_recs l)) kr W ly S Hp (ms_regs msf) (ms_mem msf) mdf 0) end.
  { unfold lf_inv_xR.
    split; [exact HJ|].
    split.
    { unfold lf_regs.
      split; [rewrite F2, Usp; f_equal; lia|].
      split; [rewrite F3, E3; reflexivity|].
      split; [rewrite F4, E4; reflexivity|].
      split; [rewrite F8, E10; reflexivity|].
      split; [rewrite F9, U10; reflexivity|].
      split; [rewrite F18, E35; reflexivity|].
      split; [rewrite F19; exact D19|].
      split; [rewrite F20; exact D20|].
      split; [rewrite F21; exact D21|].
      split; [rewrite F23, E33; reflexivity|].
      split; [rewrite F25, E25; reflexivity|].
      split; [rewrite F26, E26; reflexivity|].
      rewrite F27, E27; reflexivity. }
    split; [exact FRM0|]. split; [exact VL0|]. split; [exact VL8|]. split; [exact VL12|]. split; [exact HAWR|].
    split; [exact HVEC|].
    split; [rewrite firstn_all; rewrite Forall_forall in HFA |- *; intros r Hr; exact (proj1 (HFA r Hr))|].
    split; [intros rest Hpp; unfold lf_blks; rewrite firstn_all; exact Hpp|].
    split; [reflexivity|].
    split; [unfold hl_n; rewrite Z.sub_diag, Z.mul_0_l; exact (mle_start MT S MLAW)|].
    split; [intros a Hi Hno Herr Hpp; apply (lf_apresent_grows _ _ _ a HGrf); exact (lf_apresent_grows _ _ _ a HGr0 Hpp)|].
    split.
    { intros i Hi. rewrite K5 by lf_err_side ERF i Hi. apply K0; lf_err_side ERF i Hi. }
    split; [|exact HCNT0].
    eapply (lf_rm_cast RP S _ _ HRM0). rewrite lf_rk. lia. }
  pose proof (IND _ _ _ _ _ _ _ _ _ (le_n _) HINV) as HH. rewrite Hn0' in HH. exact HH.
Qed.
End wR.
(* the strict loop state is the R section's at R := wle *)
Lemma lf_inv_x_wle : lf_inv_x = lf_inv_xR (@wle SEGS).
Proof. reflexivity. Qed.
End c.
(* list_free's G-generic form over ARx (W_contract_x.v lf_spec_g_x): gx_ok, gx_rt and rom_out, the Section hypotheses
   on G, are conjuncts of gx_prog_x; the laws, HP0, IMGC / BLKN, PSTR, the allocator rules with their caller-context
   facts and the memmove contract stay hypotheses (all G-free). *)
Section g.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Variable MT : ameter_ops.
Variable RP : roomp.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis IMGC : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
fst (ly_img ly) <= 0x10000 /\ 0x5fb000 <= fst (ly_img ly) + snd (ly_img ly).
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Hypothesis PSTR : forall a, in_rom SEGS a -> ~ Exists (in_zr a) PST.
Hypothesis MLAW : ameter_laws MT.
Variable CTX : list (list Z).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX.
Hypothesis AFREEN : afree_null_cf_rule_c_x SEGS B PST ARx MT RP CTX.
Hypothesis HCTX_lf_loop : In [BASE + AF_fr_list_free + 0x98] CTX.
Hypothesis HCTX_lf_exit : In [BASE + AF_fr_list_free + 0xf8] CTX.
Hypothesis TL : PALib B.
Hypothesis AMOVE : amemmove_realizes_x B ARx (SIGMA WS_asan_memmove).
Theorem pb_list_free_g_x : lf_spec_g_x B PST ARx MT RP (BASE + AF_fr_list_free).
Proof.
intros G (HG & HGR & HRO & _).
change (BASE + AF_fr_list_free) with A_list_freeP.
eapply pb_list_free_x; eassumption.
Qed.
(* ---- route R: the G-generic form at a world relation R (W_contract_srlf_xR.v lf_spec_g_xR), from pb_list_free_xR as
   pb_list_free_g_x is from pb_list_free_x, under Section c's route-R hypotheses.  The strict pb_list_free_g_x keeps its
   proof. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Variable RO : (word -> option byte) -> Prop.
Hypothesis RO_ARx : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> RO mem.
Hypothesis AFREE_R : afree_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX R.
Hypothesis AFREEN_R : afree_null_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX R.
(* :1702 pb_list_free_g_x *)
Theorem pb_list_free_g_xR : lf_spec_g_xR B PST ARx R MT RP (BASE + AF_fr_list_free).
Proof.
intros G (HG & HGR & HRO & _).
change (BASE + AF_fr_list_free) with A_list_freeP.
eapply pb_list_free_xR with (RO := RO); eassumption.
Qed.
End wR.
End g.

(* ---- THE AR STATEMENTS, re-derived (route (b), step 3, CONVERSION.md (sha256 1015972e02a9; internal record) 3.): pb_list_free's and pb_list_free_g's
   statements are the AR walk's, byte-identical, now corollaries of pb_list_free_x / pb_list_free_g_x at
   ARx := ARi0 (cgif's AR with the head set empty), PST := [].  The Section takes LX0 (the laws at ARi0, a Theorem Labs lane's
   rulings (a) and HP0) in place of LAWS: the instance builds it once, W_journal_x.AR_laws_x_ARi0
   (YCbqG.AR_laws_x_of_AR ..).  The allocator rules are the caller-context forms (W_journal.v Section hc) with the
   two closed trace facts; their ARi0 twins are W_journal_x's <rule>_c_x_of_AR0.  HP0 at ARi0 is ARi0_hp0; IMGC /
   BLKN are W_kit_x.AR_imgc / AR_blkn; PSTR holds at PST = []; the memmove contract's twin is
   W_sites_x.amemmove_realizes_x_of_AR0; the bridges are W_contract_x lf_spec_x_AR0 / lf_spec_g_x_AR0. ---- *)
Section cAR.
Variable B : asyms.
Variable MT : ameter_ops.
Variable G : list (Z * Z).
Hypothesis LX0 : AR_laws_x SEGS B (ARi0 SEGS B) 0.
Hypothesis HG : gx_ok SEGS B G.
Hypothesis MLAW : ameter_laws MT.
Variable CTX : list (list Z).
Hypothesis AFREE : afree_cf_rule_c SEGS B MT CTX.
Hypothesis AFREEN : afree_null_cf_rule_c SEGS B MT CTX.
Hypothesis HCTX_lf_loop : In [BASE + AF_fr_list_free + 0x98] CTX.
Hypothesis HCTX_lf_exit : In [BASE + AF_fr_list_free + 0xf8] CTX.
Hypothesis TL : PALib B.
Hypothesis AMOVE : amemmove_realizes B (SIGMA WS_asan_memmove).
Hypothesis HGR : gx_rt B G.
Hypothesis HRO : rom_out SEGS B G.
(* the generic Sections' hypotheses at ARx := ARi0, PST := [] *)
Local Ltac lf_ari0 :=
  assert (HP0 : forall ly S Hp W mem md, ARi0 SEGS B ly S Hp W mem md -> Hp = []) by apply ARi0_hp0;
  assert (IMGC : forall ly S Hp W mem md, ARi0 SEGS B ly S Hp W mem md ->
    fst (ly_img ly) <= 0x10000 /\ 0x5fb000 <= fst (ly_img ly) + snd (ly_img ly))
    by (intros ly S Hp W mem md H; destruct H as [HAR _]; exact (AR_imgc B ly S Hp W mem md HAR));
  assert (BLKN : forall ly S Hp W mem md p n, ARi0 SEGS B ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n)
    by (intros ly S Hp W mem md p n H Hin; destruct H as [HAR _]; exact (AR_blkn B ly S Hp W mem md p n HAR Hin));
  assert (PSTR : forall a, in_rom SEGS a -> ~ Exists (in_zr a) (@nil (Z * Z))) by (intros a _ H; inversion H);
  pose proof (afree_cf_rule_c_x_of_AR0 SEGS B MT CTX AFREE) as AFREEx;
  pose proof (afree_null_cf_rule_c_x_of_AR0 SEGS B MT CTX AFREEN) as AFREENx;
  pose proof (amemmove_realizes_x_of_AR0 B _ AMOVE) as AMOVEx.
Theorem pb_list_free : lf_spec B MT G A_list_freeP.
Proof.
apply lf_spec_x_AR0. lf_ari0.
eapply pb_list_free_x with (CTX := CTX); eassumption.
Qed.
Theorem pb_list_free_g : lf_spec_g B MT (BASE + AF_fr_list_free).
Proof.
apply lf_spec_g_x_AR0. lf_ari0.
eapply pb_list_free_g_x with (CTX := CTX); eassumption.
Qed.
End cAR.
End b.
End a.
