(* reac_box_pin_parse of reac-pw/fuzz_pin, image A (fuzz_pin.asan): segment 3 of the walk, 0x80d08 -> 0x80d9c.
   Row i is found (its token is the text before the first ':' of the spec string s). The code reads the byte at
   sa + toklen and, when it is ':', the byte after it; it picks the label (sa + toklen + 1 when a byte follows the
   ':', else the row's display pointer at row + 8), stores the row in the 8 bytes at mo and the label in the 8 bytes
   at lb, sets a3 = 0 and marks the count cell's shadow byte 0xf8 again. Every instrumented check on the way passes:
   the two string bytes are inside the heap block the spec string lies in, the table's bytes are marked usable at
   every memory the allocator relation holds of, and the two out-cells are marked usable in the caller's frames;
   so the error paths 0x80e50-0x80e84 are not reached. *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YI16 YM05 YCeo.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog Require Import pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import PPgBase PPgCSpec PPgParseLib PPgParseCx PPgParse4.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the bytes of the spec string and the label, over pin_spec's functions ---- *)
Lemma pp3_zbytes_length : forall s, length (pin_zbytes s ++ [0]) = S (length s).
Proof. intros s. unfold pin_zbytes. rewrite length_app, length_map. cbn. lia. Qed.

Lemma pp3_zbytes_lt : forall s j, (j < length s)%nat -> nth j (pin_zbytes s ++ [0]) 0 = bv_unsigned (nth j s NUL).
Proof.
intros s j Hj. unfold pin_zbytes. rewrite app_nth1 by (rewrite length_map; exact Hj).
rewrite (nth_indep _ 0 ((fun b : byte => bv_unsigned b) NUL)) by (rewrite length_map; exact Hj).
rewrite map_nth. reflexivity.
Qed.

Lemma pp3_zbytes_len : forall s, nth (length s) (pin_zbytes s ++ [0]) 0 = 0.
Proof.
intros s. unfold pin_zbytes. rewrite app_nth2 by (rewrite length_map; lia).
rewrite length_map, Nat.sub_diag. reflexivity.
Qed.

Lemma pp3_colon_byte : forall s, (colon_idx s < length s)%nat -> bv_unsigned (nth (colon_idx s) s NUL) = COLON.
Proof.
intros s Hlt. destruct (colon_idx_at s Hlt) as (b & Hb & Hc).
rewrite (nth_error_nth s (colon_idx s) NUL Hb). exact Hc.
Qed.

Lemma pp3_nonnul_byte : forall s j, ~ In NUL s -> (j < length s)%nat -> bv_unsigned (nth j s NUL) <> 0.
Proof.
intros s j Hs Hj E. apply Hs. assert (Hin : In (nth j s NUL) s) by (apply nth_In; exact Hj).
replace (nth j s NUL) with NUL in Hin; [exact Hin|]. apply bv_eq. rewrite E. reflexivity.
Qed.

Lemma pp3_label_some : forall s, (S (colon_idx s) < length s)%nat -> pin_label_off s = Some (S (colon_idx s)).
Proof. intros s H. unfold pin_label_off. apply Nat.ltb_lt in H. rewrite H. reflexivity. Qed.

Lemma pp3_label_none : forall s, ~ (S (colon_idx s) < length s)%nat -> pin_label_off s = None.
Proof. intros s H. unfold pin_label_off. destruct (Nat.ltb_spec (S (colon_idx s)) (length s)); [lia | reflexivity]. Qed.

(* The three shapes of the bytes the code reads at sa + toklen and sa + toklen + 1 (toklen = colon_idx s). *)
Lemma pp3_cases : forall s, ~ In NUL s ->
((colon_idx s < length s)%nat /\ (S (colon_idx s) < length s)%nat /\
 nth (colon_idx s) (pin_zbytes s ++ [0]) 0 = COLON /\
 1 <= nth (S (colon_idx s)) (pin_zbytes s ++ [0]) 0 < 256 /\ pin_label_off s = Some (S (colon_idx s))) \/
((colon_idx s < length s)%nat /\ S (colon_idx s) = length s /\
 nth (colon_idx s) (pin_zbytes s ++ [0]) 0 = COLON /\
 nth (S (colon_idx s)) (pin_zbytes s ++ [0]) 0 = 0 /\ pin_label_off s = None) \/
(colon_idx s = length s /\ nth (colon_idx s) (pin_zbytes s ++ [0]) 0 = 0 /\ pin_label_off s = None).
Proof.
intros s Hs. pose proof (colon_idx_le s) as Hle.
destruct (Nat.ltb_spec (colon_idx s) (length s)) as [Hlt|Hge].
- destruct (Nat.ltb_spec (S (colon_idx s)) (length s)) as [Hlt2|Hge2].
  + left. split; [exact Hlt|]. split; [exact Hlt2|].
    rewrite (pp3_zbytes_lt s _ Hlt), (pp3_zbytes_lt s _ Hlt2), (pp3_colon_byte s Hlt).
    split; [reflexivity|]. split; [|exact (pp3_label_some s Hlt2)].
    pose proof (pp3_nonnul_byte s _ Hs Hlt2). pose proof (bv_unsigned_in_range 8 (nth (S (colon_idx s)) s NUL)) as R.
    unfold bv_modulus in R. cbn in R. lia.
  + right; left. assert (HE : S (colon_idx s) = length s) by lia.
    split; [exact Hlt|]. split; [exact HE|].
    rewrite (pp3_zbytes_lt s _ Hlt), (pp3_colon_byte s Hlt), HE, pp3_zbytes_len.
    split; [reflexivity|]. split; [reflexivity|]. apply pp3_label_none. lia.
- right; right. assert (HE : colon_idx s = length s) by lia.
  split; [exact HE|]. rewrite HE, pp3_zbytes_len. split; [reflexivity|]. apply pp3_label_none. lia.
Qed.
(* ---- the walk ---- *)
(* A fact kept out of lia's sight: lia case-splits every disjunction (and negated conjunction) of the context, so
   the walk states such facts under this name and unfolds it only in a cleared context. *)
Definition p3w (P : Prop) : Prop := P.
(* add a region r to the state: rok proves region_ok, dtac each disjointness goal (in a cleared context) *)
Ltac p3_add HS AG r rok dtac :=
lazymatch type of HS with st_ok _ ?Ev _ _ =>
let HS3 := fresh "HS3" in
pose proof (ast_ok_add_region tfibsegs Ev _ _ r HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
  first [rok | match goal with |- ?g => idtac "P3ADD-ROK-FAIL" g end; fail 1])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
  cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; ewpeel; evalE AG;
  repeat split; first [dtac | match goal with |- ?g => idtac "P3ADD-DISJ-FAIL" g end; fail 1])) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
(* the value of an atom in the current valuation, from its value in an earlier one *)
Ltac p3_now HS H Hn :=
lazymatch type of HS with st_ok _ ?Ev _ _ =>
lazymatch type of H with ew _ ?n = ?v => assert (Hn : ew Ev n = v) by (ewpeel; exact H) end end.
(* a region of the state, by its base atom *)
Ltac p3_region HS n R :=
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let j := idx_of_base rs n in let j := eval vm_compute in j in
let r := eval vm_compute in (nth j rs got_region) in
pose proof (st_ok_region_nth Ex ssx msx j r HS ltac:(vm_compute; reflexivity)) as R end.
(* an out-cell byte is a byte of a frame the caller owns (awr_byte's in_frames clause) *)
Ltac p3_awr_oc Hm Hl' EFA :=
right; right; right;
first [ lazymatch type of Hm with In (?c, ?p) _ => exists c, p end;
        split; [right; exact Hm | left; unfold in_zr; cbn [fst snd]; rewrite ?EFA; lia]
      | lazymatch type of Hl' with In (?c, ?p) _ => exists c, p end;
        split; [right; exact Hl' | left; unfold in_zr; cbn [fst snd]; rewrite ?EFA; lia] ].
(* the excluded set of the kept-memory fact holds of an out-cell byte a (Hr : its range) of a live call *)
Ltac p3_oc Hl :=
try unfold pp_oc; cbn [c_sa c_mo c_lb]; split; [exact Hl | unfold pin_out_cell; lia].
(* the 8-byte value a run left in the out-cell region n: its one chunk at offset 0 (vt proves its value) *)
Ltac p3_cellv HS n En v V vt :=
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
lazymatch type of En with ew _ _ = Z_to_bv 64 ?p =>
let R := fresh "R" in p3_region HS n R;
let Rc := fresh "Rc" in
unfold region_ok in R; cbn [YP09.r_chunks YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in R;
destruct R as (_ & _ & _ & Rc); apply Forall_inv in Rc;
let Enc := fresh "Enc" in
assert (Enc : ew Ex n = Z_to_bv 64 p) by (ewpeel; exact En);
rewrite Enc, unsigned_lit_small in Rc by lia;
assert (V : val_mem tfibsegs (ms_mem msx) p 8 v);
[ replace p with (p + 0) by (clear; lia);
  eapply (val_of_chunk_ok tfibsegs Ex (ms_mem msx) p 0 8%N); [exact Rc | vt | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia]
| clear Rc Enc ] end end.
(* 0x80d94 .. 0x80d9c and the hand-off to ss_P4, from the state the token runner leaves at 0x80d94: the count
   cell's shadow byte back to 0xf8 (the shadow region writable for that store), the out-cells' values read off
   the regions 11 and 12 (vlab proves the label chunk's value), a3 the result word 0, the frame writable again. *)
Ltac p3_end HS HJ HKE HARc HARN Hfrs HPERM ELF HOCF AG F FL Hfin EFA LAWS fpos E88 E75 Hm Hl' Hl RC4 E70 E87 Hres
  E11n E12n E102 vlab :=
let HFp3 := fresh "HFp3" in let HFS3 := fresh "HFS3" in
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos (proj1 HJ) Hfin) as (_ & _ & HFp3 & HFS3);
change (fs_frame_bytes 0) with 64 in HFp3, HFS3; change (64 / 8) with 8 in HFS3;
rewrite !EFA in HFp3, HFS3; fold F in HFp3, HFS3;
pp_fs_rw HS E88 HFS3;
aj_run_to tfibtbl_lib_ok HS HJ 0x80d9c;
try (lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ => ppAWR AG fpos F EFA ltac:(p3_awr_oc Hm Hl' EFA) end);
pp_keep HKE HARc HARN Hfrs HPERM ELF HOCF AG F FL ltac:(p3_oc Hl);
pp_fs_ro HS;
lazymatch type of Hres with _ = Some (?rowv, ?labv) =>
let Vm := fresh "Vm" in let Vl := fresh "Vl" in
p3_cellv HS 11%nat E11n rowv Vm ltac:(rewrite sv_denot_SOff0; ewpeel; exact E102);
p3_cellv HS 12%nat E12n labv Vl vlab;
let HFp4 := fresh "HFp4" in let HFS4 := fresh "HFS4" in
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos (proj1 HJ) Hfin) as (_ & _ & HFp4 & HFS4);
change (fs_frame_bytes 0) with 64 in HFp4; rewrite !EFA in HFp4; fold F in HFp4;
pp_fr_rw HS E75 F HFp4;
let E104 := fresh "E104" in
add_atom_win HS 104%nat (Z_to_bv 64 0) E104;
let R13 := fresh "R13" in rreg HS (13%bv : bv 5) R13;
ws_pin HS (13%bv : bv 5) (SOff 104 0) R13
  ltac:(rewrite E104, Z.add_0_r, Z_to_bv_bv_unsigned; apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity);
ra_join_win HS ss_P4 PW_P4 pp_deads_P4_bv ltac:(idtac);
pp_hand2 RC4 HS AG E70 E75 E87 E88;
split;
[ unfold PN_rc, PW_P4; ewpeel; rewrite E104, Hres; reflexivity
| let x := fresh "x" in let y := fresh "y" in let Hx := fresh "Hx" in
  intros x y Hx; rewrite Hres in Hx; injection Hx as <- <-; split; [exact Vm | exact Vl] ] end.
(* the instrumented checks' obligations: the string bytes from the heap block, the display pointer from the table *)
Ltac p3_obl HARN HbmN E401 E102 E32n HcRA Trow :=
let LAWS := rnLAWS in
lazymatch goal with
| |- range_addressable _ (U ?Ex _) (U _ (SOff 401 ?c)) ?len =>
  lazymatch type of E401 with _ = Z_to_bv 64 ?v =>
  rewrite (U_atom_off Ex 401 v c ltac:(ewpeel; exact E401) ltac:(lia) ltac:(lia));
  eapply (obl_of_block tfibsegs _ LAWS _ _ _ _ _ Ex PPBx _ len _ _ HARN HbmN);
  [ unfold PPBx; rewrite (U_atom Ex 32 SB ltac:(ewpeel; exact E32n) ltac:(unfold SB; lia)); reflexivity | lia | lia ] end
| |- range_addressable _ (U ?Ex _) (U _ (SOff 102 8)) 8 =>
  lazymatch type of E102 with _ = Z_to_bv 64 ?v =>
  rewrite (U_atom_off Ex 102 v 8 ltac:(ewpeel; exact E102) ltac:(clear - Trow; unfold row_addr, CAT_ROW, CAT_BYTES in *; lia)
    ltac:(clear - Trow; unfold row_addr, CAT_ROW, CAT_BYTES in *; lia));
  unfold PPBx; rewrite (U_atom Ex 32 SB ltac:(ewpeel; exact E32n) ltac:(unfold SB; lia));
  rewrite <- (aview_rd_of tfibsegs); change SB with SHADOW_OFF;
  eapply range_addressable_sub;
  [ exact HcRA | clear - Trow; unfold row_addr, CAT_ROW, CAT_BYTES in *; lia | clear - Trow; unfold row_addr, CAT_ROW, CAT_BYTES in *; lia ] end
end.
(* the token runner from 0x80d08 to 0x80d94 (the label's bytes, the out-cell checks and stores), its write ranges,
   its check obligations, and the kept-memory fact carried to its end *)
Ltac p3_run HS HJ HKE HARc HARN Hfrs HPERM ELF HOCF AG F FL fpos EFA Hm Hl' Hl HbmN E401 E102 E32n HcRA Trow SHOK :=
aj_run_to_tok tfibtbl_lib_ok HS HJ SHOK PPBspan 0x80d94;
try (lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ => ppAWR AG fpos F EFA ltac:(p3_awr_oc Hm Hl' EFA) end);
try (p3_obl HARN HbmN E401 E102 E32n HcRA Trow);
pp_keep HKE HARc HARN Hfrs HPERM ELF HOCF AG F FL ltac:(p3_oc Hl).

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.  Variable MT : ameter_ops.
Hypothesis TL : TfibLib B.                Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis FFL : frame_flag_lawP tfibsegs B.
Variables RLO RHI cat : Z.  Variables TP DP : nat -> Z.
Hypothesis RELRO : forall a, RLO <= a < RHI -> in_img tfibsegs a.
Hypothesis CATIMG : forall x, cat <= x < cat + CAT_BYTES -> in_img tfibsegs x.
Lemma pp_seg3 : PP_seg3 B MT RLO RHI cat TP DP.
Proof.
unfold PP_seg3. intros RC4.
pp_prelude.
pp_fr_ro HS.
destruct HINV as (i & Hl & Hsne & Hi & E100 & E102 & Htok & Hrow).
unfold PN_tl, PN_row in E100, E102.
pose proof (proj1 HJ0) as HARc.
pose proof HJ0 as (_ & _ & _ & _ & _ & Hfrsc & _).
assert (ELF : ly_F lyN = ly_F lyc) by (eapply pp_lyF; [exact HJ0 | exact HJ]).
assert (HOCF : pp_oc_frames lyc Sc (pin_parse_live sa mo lb) mo lb cidm posm cidl posl).
{ intros Hl0. destruct (Hlive Hl0) as (_ & _ & _ & Hm & _ & _ & Hm1 & Hm2 & Hl' & _ & _ & Hl1 & Hl2 & _).
  rewrite Hfrsc. split; [apply in_or_app; left; exact Hm|]. split; [exact Hm1|]. split; [exact Hm2|].
  split; [apply in_or_app; left; exact Hl'|]. split; [exact Hl1 | exact Hl2]. }
ppLOW HS AG E10 E10n. ppLOW HS AG E11 E11n. ppLOW HS AG E12 E12n. ppLOW HS AG E32 E32n.
destruct (proj1 (pp_live_iff sa mo lb) Hl) as (Hsanz & Hmonz & Hlbnz).
destruct (Hstr Hsanz) as (HSTR & b & m & Hbm & Hb1 & Hb2).
pose proof HSTR as (Hnul & _ & Hsa63 & Hlen32 & HG8 & _ & _ & _ & _ & HOFF).
destruct (Hlive Hl) as (Hmo8 & Hlb8 & Hmolb0 & Hm & _ & _ & Hm1 & Hm2 & Hl' & _ & _ & Hl1 & Hl2 & HAFm & HAFl & HOS & HOSS).
assert (Hmolb : p3w (mo + 8 <= lb \/ lb + 8 <= mo)) by exact Hmolb0. clear Hmolb0.
destruct (HOCF Hl) as (HmSc & _ & _ & HlSc & _ & _).
(* the facts the disjointness goals need, each stated under p3w *)
pose proof (colon_idx_le s) as Htl.
destruct (frames_bounds tfibsegs B LAWS lyc Sc W memc mdc cidm posm HARc HmSc) as (M4096 & Mce & Mapp).
destruct (frames_bounds tfibsegs B LAWS lyc Sc W memc mdc cidl posl HARc HlSc) as (L4096 & Lce & Lapp).
pose proof (frm_off_img B lyc Sc W memc mdc cidm posm HARc HmSc) as Mimg.
pose proof (frm_off_img B lyc Sc W memc mdc cidl posl HARc HlSc) as Limg.
pose proof (pz_own_sep tfibsegs B LAWS lyN SN WN (ms_mem msN) mdN 0 fpos Sc cidm posm HARN Hfrs HmSc) as MF.
pose proof (pz_own_sep tfibsegs B LAWS lyN SN WN (ms_mem msN) mdN 0 fpos Sc cidl posl HARN Hfrs HlSc) as LF.
assert (HbmN : In (b, m) (ablocks B lyN SN)) by (apply (Permutation_in _ (Permutation_sym HPERM)); exact Hbm).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HARN HbmN) as (_ & Hb4096 & Hbce & Hbapp & _).
pose proof (blk_off_img B _ _ _ _ _ b m HARN HbmN) as Hbimg.
pose proof (sep_block_frame tfibsegs B LAWS _ _ _ _ _ b m 0 fpos HARN HbmN Hfin) as HbF.
(* the table at the current memory (F-RO-LAW) *)
pose proof (pp_arodata_kept B RLO RHI lyc Sc W memc WN (ms_mem msN) _ _ _ RELRO HKE HROD) as HRODN.
destruct (pin_ro_law_at tfibsegs B RLO RHI cat TP DP PP_COLON _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrolaw HJ HRODN) as (HCATN & _).
pose proof HCATN as (Hc0 & Hc8 & Hc63 & _ & HcRA & Hrows).
destruct (Hrows i Hi) as (_ & HDPv & _ & HDPr & _).
assert (HiZ : 0 <= Z.of_nat i <= 10) by (clear - Hi; unfold CAT_N in Hi; lia).
assert (Trow : cat <= row_addr cat i /\ row_addr cat i + 16 <= cat + CAT_BYTES /\ 0 < cat /\ cat + CAT_BYTES <= 2 ^ 63)
by (clear - Hc0 Hc63 HiZ; unfold row_addr, CAT_ROW, CAT_BYTES in *; lia).
pose proof (CATIMG (row_addr cat i + 8) ltac:(clear - Trow; unfold CAT_BYTES in *; lia)) as T8.
pose proof (CATIMG (row_addr cat i + 15) ltac:(clear - Trow; unfold CAT_BYTES in *; lia)) as T15.
apply tfib_img_range in T8, T15. unfold TFIB_IMG_LO, TFIB_IMG_END in T8, T15.
destruct Hcatst as (Hcst & _).
pose proof (Hcst (row_addr cat i + 8) ltac:(clear - Trow; unfold CAT_BYTES in *; lia)) as S8.
pose proof (Hcst (row_addr cat i + 15) ltac:(clear - Trow; unfold CAT_BYTES in *; lia)) as S15.
assert (TSt : p3w (row_addr cat i + 16 <= spZ regs - 8400 \/ spZ regs <= row_addr cat i + 8))
by (clear - S8 S15; unfold p3w; change T_parse_STK with 8400 in S8, S15; lia). clear S8 S15.
assert (Moff : p3w (mo + 8 <= YImgTop.IMG_LO \/ YImgTop.IMG_TOP <= mo))
by (clear - Mimg Hm1 Hm2; unfold p3w, off_img in *; lia).
assert (Loff : p3w (lb + 8 <= YImgTop.IMG_LO \/ YImgTop.IMG_TOP <= lb))
by (clear - Limg Hl1 Hl2; unfold p3w, off_img in *; lia).
assert (Foff : p3w (F + 64 <= YImgTop.IMG_LO \/ YImgTop.IMG_TOP <= F)) by (clear - HFimg; unfold p3w, off_img in *; exact HFimg).
assert (Boff : p3w (b + req_size m <= YImgTop.IMG_LO \/ YImgTop.IMG_TOP <= b)) by (clear - Hbimg; unfold p3w, off_img in *; exact Hbimg).
assert (MS : p3w (mo + 8 <= 2147446784 \/ 17594333495296 <= mo))
by (clear - Mapp Hm1 Hm2; unfold p3w, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia).
assert (LS : p3w (lb + 8 <= 2147446784 \/ 17594333495296 <= lb))
by (clear - Lapp Hl1 Hl2; unfold p3w, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia).
assert (BS : p3w (b + req_size m <= 2147446784 \/ 17594333495296 <= b))
by (clear - Hbapp; unfold p3w, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia).
assert (MFd : p3w (mo + 8 <= F \/ F + 64 <= mo))
by (clear - MF Hm1 Hm2 EFA; unfold p3w, zdisjoint, frame_rng in *; cbn [fst snd] in MF; change (fs_frame_bytes 0) with 64 in MF; rewrite !EFA in MF; fold F in MF; lia).
assert (LFd : p3w (lb + 8 <= F \/ F + 64 <= lb))
by (clear - LF Hl1 Hl2 EFA; unfold p3w, zdisjoint, frame_rng in *; cbn [fst snd] in LF; change (fs_frame_bytes 0) with 64 in LF; rewrite !EFA in LF; fold F in LF; lia).
assert (BFd : p3w (b + req_size m <= F \/ F + 64 <= b))
by (clear - HbF EFA; unfold p3w, zdisjoint in *; cbn [fst snd] in HbF; change (fs_frame_bytes 0) with 64 in HbF; rewrite !EFA in HbF; fold F in HbF; exact HbF).
clear MF LF HbF Mimg Limg Hbimg Mapp Lapp.
assert (MSt : p3w (mo + 8 <= spZ regs - 8400 \/ spZ regs <= mo))
by (pose proof (HOS mo ltac:(left; clear; lia)) as X0; pose proof (HOS (mo + 7) ltac:(left; clear; lia)) as X7;
    clear - X0 X7; unfold p3w; change T_parse_STK with 8400 in X0, X7; lia).
assert (LSt : p3w (lb + 8 <= spZ regs - 8400 \/ spZ regs <= lb))
by (pose proof (HOS lb ltac:(right; clear; lia)) as X0; pose proof (HOS (lb + 7) ltac:(right; clear; lia)) as X7;
    clear - X0 X7; unfold p3w; change T_parse_STK with 8400 in X0, X7; lia).
assert (HF8r : 512 <= F / 8 /\ F / 8 + 8 <= 17592184995840).
{ split; [exact HF8lo|].
  assert (Hd : (F + 8 * 8) / 8 <= 140737479966720 / 8) by (apply Z.div_le_mono; clear - HFceil C1; lia).
  rewrite Z.div_add in Hd by lia. change (140737479966720 / 8) with 17592184995840 in Hd. clear - Hd; lia. }
(* the two out-cells' bytes at the current memory, and their shadow bytes (kept: caller-frame shadow) *)
assert (HmSN : In (cidm, posm) (frames SN)) by (rewrite Hfrs; right; exact HmSc).
assert (HlSN : In (cidl, posl) (frames SN)) by (rewrite Hfrs; right; exact HlSc).
destruct (al_frames _ _ LAWS _ _ _ _ _ cidm posm HARN HmSN) as (_ & _ & HPm & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ cidl posl HARN HlSN) as (_ & _ & HPl & _).
rewrite !EFA in HPm, HPl.
assert (RAm : range_addressable (aview tfibsegs (w_H WN) (ms_mem msN)) SHADOW_OFF mo 8).
{ apply (pz_kept_ra tfibsegs B LAWS lyc Sc W memc mdc WN (ms_mem msN) _ _ _ cidm posm mo 8 HARc HKE HmSc Hm1 Hm2);
  [| exact (proj2 (proj2 HAFm))].
  intros x Hx (_ & Ho). unfold pin_out_cell, shadow_addr, SHADOW_OFF in Ho.
  assert (X8 : x / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia). assert (X0 : 0 <= x / 8) by (apply Z.div_pos; lia).
  clear - Ho X8 X0 MS LS; unfold p3w in *; lia. }
assert (RAl : range_addressable (aview tfibsegs (w_H WN) (ms_mem msN)) SHADOW_OFF lb 8).
{ apply (pz_kept_ra tfibsegs B LAWS lyc Sc W memc mdc WN (ms_mem msN) _ _ _ cidl posl lb 8 HARc HKE HlSc Hl1 Hl2);
  [| exact (proj2 (proj2 HAFl))].
  intros x Hx (_ & Ho). unfold pin_out_cell, shadow_addr, SHADOW_OFF in Ho.
  assert (X8 : x / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia). assert (X0 : 0 <= x / 8) by (apply Z.div_pos; lia).
  clear - Ho X8 X0 MS LS; unfold p3w in *; lia. }
(* the string's bytes at sa + toklen and sa + toklen + 1 at the current memory (the block is kept) *)
assert (HVs : forall j, (j <= length s)%nat -> val_mem tfibsegs (mrestrict (w_H WN) (ms_mem msN)) (sa + Z.of_nat j) 1 (nth j (pin_zbytes s ++ [0]) 0)).
{ intros j Hj. destruct (HG8 j ltac:(rewrite pp3_zbytes_length; lia)) as (V & _).
  apply (val_mem_kept tfibsegs (w_H W) (w_H WN) memc (ms_mem msN)); [|exact V].
  intros q Hq. cbn [Z.of_nat Pos.of_succ_nat] in Hq. replace (sa + Z.of_nat j + q) with (b + (sa + Z.of_nat j - b)) by lia.
  pose proof HKE as (_ & K2 & _). apply (K2 b m (sa + Z.of_nat j - b) Hbm); [lia|].
  intros (_ & Ho). apply (HOSS (b + (sa + Z.of_nat j - b)) Ho). lia. }
assert (HVr : forall j, (j <= length s)%nat -> 0 <= nth j (pin_zbytes s ++ [0]) 0 < 256)
by (intros j Hj; exact (proj2 (HG8 j ltac:(rewrite pp3_zbytes_length; lia)))).
(* atoms: 401 = sa + toklen (with the alias the engine meets at 0x80d08 `add a0,s5,s9`), 403 = DP i *)
add_atom_win HS 401%nat (Z_to_bv 64 (sa + Z.of_nat (colon_idx s))) E401.
AWalkFw2.add_fact HS 401%nat 4096 140737488355326 E401 ltac:(lia).
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
let HS3 := fresh "HS3" in
pose proof (st_ok_add_alias tfibsegs Ev ssx msx (SAlu ALU_ADD (SOff 10 0) (SOff 100 0)) (SOff 401 0) HS
  ltac:(rewrite (denot_add2 Ev 10 100 sa (Z.of_nat (colon_idx s)) ltac:(ewpeel; exact E10n) ltac:(ewpeel; exact E100)
          ltac:(lia) ltac:(lia) ltac:(lia));
        rewrite sv_denot_SOff0, E401; reflexivity)) as HS3; clear HS; rename HS3 into HS; norm_ss HS end.
add_atom_win HS 403%nat (Z_to_bv 64 (DP i)) E403.
(* the regions: the two out-cells (writable), the row's display pointer *)
p3_add HS AG (YP09.mkRegion (Some 11%nat) 0 8 0 8 [])
ltac:(ewpeel; rewrite E11n, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
  intros o Ho; apply (apresent_writable tfibsegs); apply (proj1 (HPm (mo + o) ltac:(lia))))
ltac:(clear - MS MFd MSt HF8r Hsp1; unfold p3w in *; lia).
p3_add HS AG (YP09.mkRegion (Some 12%nat) 0 8 0 8 [])
ltac:(ewpeel; rewrite E12n, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
  intros o Ho; apply (apresent_writable tfibsegs); apply (proj1 (HPl (lb + o) ltac:(lia))))
ltac:(clear - LS LFd LSt HF8r Hsp1 Hmolb; unfold p3w in *; lia).
p3_add HS AG (YP09.mkRegion (Some 102%nat) 8 16 0 0 [YP09.mkChunk 8 (CVal 8 (SOff 403 0))])
ltac:(ewpeel; rewrite E102, unsigned_lit_small by (clear - Trow Hc0; unfold row_addr, CAT_ROW, CAT_BYTES in *; lia);
  split; [lia|]; split; [lia|];
  split; [intros oo Hoo; lia|]; apply Forall_cons; [|apply Forall_nil];
  apply (chunk_ok_val tfibsegs _ _ (row_addr cat i) 8 8 (SOff 403 0) (DP i));
  [rewrite sv_denot_SOff0; ewpeel; exact E403 | cbn; lia | cbn; lia | exact HDPv])
ltac:(clear - T8 T15 Moff Loff Foff TSt HF8r Hsp1; unfold p3w, YImgTop.IMG_LO, YImgTop.IMG_TOP in *; lia).
(* the string's place: apart from the table (image), the out-cells (contract), the frame, its shadow and the stack *)
pose proof (HOFF (sa + Z.of_nat (colon_idx s)) ltac:(lia)) as So0. change T_parse_STK with 8400 in So0.
pose proof (HOSS (sa + Z.of_nat (colon_idx s))) as SSt0. unfold pin_out_cell in SSt0.
assert (STR0 : p3w (~ (spZ regs - 8400 <= sa + Z.of_nat (colon_idx s) < spZ regs) /\
  ~ (mo <= sa + Z.of_nat (colon_idx s) < mo + 8) /\ ~ (lb <= sa + Z.of_nat (colon_idx s) < lb + 8)))
by (clear - So0 SSt0 Htl; unfold p3w; split; [exact So0|];
    split; intros X; apply SSt0; [first [left; exact X | right; exact X] | lia | first [left; exact X | right; exact X] | lia]).
clear So0 SSt0.
assert (STRb : b <= sa /\ sa + Z.of_nat (length s) + 1 <= b + req_size m /\ (colon_idx s <= length s)%nat) by (clear - Hb1 Hb2 Htl; lia).
(* atom 402: the byte after the ':' (used in the first case only) *)
add_atom_win HS 402%nat (Z_to_bv 64 (nth (Datatypes.S (colon_idx s)) (pin_zbytes s ++ [0]) 0)) E402.
(* the token runner's shadow entries for the two out-cells *)
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (SHOK : sh_ok tfibsegs PPBx [mkSHE 11 0 8; mkSHE 12 0 8] Ev (mrestrict (w_H WN) (ms_mem msN)))
by (constructor; [|constructor; [|constructor]];
    [ apply (shent_ok_of_range tfibsegs (w_H WN) (ms_mem msN) Ev PPBx 11 mo 8 mo 0 8 RAm);
      [ unfold PPBx; rewrite (U_atom Ev 32 SB ltac:(ewpeel; exact E32n) ltac:(unfold SB; lia)); reflexivity
      | rewrite (U_atom Ev 11 mo ltac:(ewpeel; exact E11n) ltac:(lia)); reflexivity | lia | lia
      | intros x Hx; cbn [Z.min Z.max] in Hx; clear - Hx MS; unfold p3w, SHADOW_OFF in *; lia ]
    | apply (shent_ok_of_range tfibsegs (w_H WN) (ms_mem msN) Ev PPBx 12 lb 8 lb 0 8 RAl);
      [ unfold PPBx; rewrite (U_atom Ev 32 SB ltac:(ewpeel; exact E32n) ltac:(unfold SB; lia)); reflexivity
      | rewrite (U_atom Ev 12 lb ltac:(ewpeel; exact E12n) ltac:(lia)); reflexivity | lia | lia
      | intros x Hx; cbn [Z.min Z.max] in Hx; clear - Hx LS; unfold p3w, SHADOW_OFF in *; lia ] ]) end.
pose proof (pp3_cases s Hnul) as [(Hc1 & Hc2 & Hb0 & Hb1r & Hlab) | [(Hc1 & Hc2 & Hb0 & Hz1 & Hlab) | (Hc1 & Hb0 & Hlab)]].
- (* ':' and a byte after it: the label is sa + toklen + 1 *)
  AWalkFw2.add_fact HS 402%nat 1 255 E402 ltac:(lia).
  pose proof (HOFF (sa + Z.of_nat (colon_idx s) + 1) ltac:(lia)) as So1. change T_parse_STK with 8400 in So1.
  pose proof (HOSS (sa + Z.of_nat (colon_idx s) + 1)) as SSt1. unfold pin_out_cell in SSt1.
  assert (STR1 : p3w (~ (spZ regs - 8400 <= sa + Z.of_nat (colon_idx s) + 1 < spZ regs) /\
    ~ (mo <= sa + Z.of_nat (colon_idx s) + 1 < mo + 8) /\ ~ (lb <= sa + Z.of_nat (colon_idx s) + 1 < lb + 8)))
  by (clear - So1 SSt1 Htl Hc2; unfold p3w; split; [exact So1|];
      split; intros X; apply SSt1; [first [left; exact X | right; exact X] | lia | first [left; exact X | right; exact X] | lia]).
  clear So1 SSt1.
  p3_add HS AG (YP09.mkRegion (Some 401%nat) 0 2 0 0 [YP09.mkChunk 0 (CVal 1 (SLit COLON)); YP09.mkChunk 1 (CVal 1 (SOff 402 0))])
  ltac:(ewpeel; rewrite E401, unsigned_lit_small by lia; split; [lia|]; split; [lia|];
    split; [intros oo Hoo; lia|]; apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
    [ apply (chunk_ok_val tfibsegs _ _ (sa + Z.of_nat (colon_idx s)) 0 1 (SLit COLON) COLON);
      [reflexivity | change (2 ^ (8 * Z.of_N 1)) with 256; unfold COLON; lia | cbn; lia |
       rewrite Z.add_0_r, <- Hb0; exact (HVs (colon_idx s) ltac:(lia))]
    | apply (chunk_ok_val tfibsegs _ _ (sa + Z.of_nat (colon_idx s)) 1 1 (SOff 402 0) (nth (Datatypes.S (colon_idx s)) (pin_zbytes s ++ [0]) 0));
      [rewrite sv_denot_SOff0; ewpeel; exact E402 | change (2 ^ (8 * Z.of_N 1)) with 256; lia | cbn; lia |
       replace (sa + Z.of_nat (colon_idx s) + 1) with (sa + Z.of_nat (Datatypes.S (colon_idx s))) by lia;
       exact (HVs (Datatypes.S (colon_idx s)) ltac:(lia))] ])
  ltac:(first
    [ clear - Boff T8 T15 STRb Hc2; unfold p3w, YImgTop.IMG_LO, YImgTop.IMG_TOP in *; lia
    | clear - STR0 STR1; unfold p3w in *; lia
    | clear - BS STRb Hc2 HF8r; unfold p3w in *; lia
    | clear - BFd STRb Hc2; unfold p3w in *; lia
    | clear - STR0 STR1 Hsp1; unfold p3w in *; lia ]).
  (* 0x80d08-0x80d90: the two checked string bytes, the out-cell checks and stores, a3 = 0; to 0x80d94 *)
  p3_run HS HJ HKE HARc HARN Hfrs HPERM ELF HOCF AG F FL fpos EFA Hm Hl' Hl HbmN E401 E102 E32n HcRA Trow SHOK.
  assert (Hres : pin_parse_res cat DP sa mo lb s = Some (row_addr cat i, sa + Z.of_nat (colon_idx s) + 1)).
  { rewrite (pp_res_live cat DP sa mo lb s i Hl Hrow), (pp_label_at_some DP sa s i _ Hlab).
    replace (sa + Z.of_nat (colon_idx s) + 1) with (sa + Z.of_nat (Datatypes.S (colon_idx s))) by (clear; lia). reflexivity. }
  p3_end HS HJ HKE HARc HARN Hfrs HPERM ELF HOCF AG F FL Hfin EFA LAWS fpos E88 E75 Hm Hl' Hl RC4 E70 E87 Hres
    E11n E12n E102
    ltac:(cbn [sv_denot]; ewpeel; rewrite E401, unsigned_lit_small by lia;
          first [reflexivity | apply (f_equal (Z_to_bv 64)); clear; lia]).
- (* ':' and the NUL after it: the label is the row's display pointer *)
  pose proof (HOFF (sa + Z.of_nat (colon_idx s) + 1) ltac:(lia)) as So1. change T_parse_STK with 8400 in So1.
  pose proof (HOSS (sa + Z.of_nat (colon_idx s) + 1)) as SSt1. unfold pin_out_cell in SSt1.
  assert (STR1 : p3w (~ (spZ regs - 8400 <= sa + Z.of_nat (colon_idx s) + 1 < spZ regs) /\
    ~ (mo <= sa + Z.of_nat (colon_idx s) + 1 < mo + 8) /\ ~ (lb <= sa + Z.of_nat (colon_idx s) + 1 < lb + 8)))
  by (clear - So1 SSt1 Htl Hc2; unfold p3w; split; [exact So1|];
      split; intros X; apply SSt1; [first [left; exact X | right; exact X] | lia | first [left; exact X | right; exact X] | lia]).
  clear So1 SSt1.
  p3_add HS AG (YP09.mkRegion (Some 401%nat) 0 2 0 0 [YP09.mkChunk 0 (CVal 1 (SLit COLON)); YP09.mkChunk 1 (CVal 1 (SLit 0))])
  ltac:(ewpeel; rewrite E401, unsigned_lit_small by lia; split; [lia|]; split; [lia|];
    split; [intros oo Hoo; lia|]; apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
    [ apply (chunk_ok_val tfibsegs _ _ (sa + Z.of_nat (colon_idx s)) 0 1 (SLit COLON) COLON);
      [reflexivity | change (2 ^ (8 * Z.of_N 1)) with 256; unfold COLON; lia | cbn; lia |
       rewrite Z.add_0_r, <- Hb0; exact (HVs (colon_idx s) ltac:(lia))]
    | apply (chunk_ok_val tfibsegs _ _ (sa + Z.of_nat (colon_idx s)) 1 1 (SLit 0) 0);
      [reflexivity | change (2 ^ (8 * Z.of_N 1)) with 256; lia | cbn; lia |
       replace (sa + Z.of_nat (colon_idx s) + 1) with (sa + Z.of_nat (Datatypes.S (colon_idx s))) by lia;
       let V1 := fresh "V1" in pose proof (HVs (Datatypes.S (colon_idx s)) ltac:(lia)) as V1; rewrite Hz1 in V1; exact V1] ])
  ltac:(first
    [ clear - Boff T8 T15 STRb Hc2; unfold p3w, YImgTop.IMG_LO, YImgTop.IMG_TOP in *; lia
    | clear - STR0 STR1; unfold p3w in *; lia
    | clear - BS STRb Hc2 HF8r; unfold p3w in *; lia
    | clear - BFd STRb Hc2; unfold p3w in *; lia
    | clear - STR0 STR1 Hsp1; unfold p3w in *; lia ]).
  (* 0x80d08-0x80d90: the two checked string bytes, the check of row + 8 and its load, the out-cells; to 0x80d94 *)
  p3_run HS HJ HKE HARc HARN Hfrs HPERM ELF HOCF AG F FL fpos EFA Hm Hl' Hl HbmN E401 E102 E32n HcRA Trow SHOK.
  assert (Hres : pin_parse_res cat DP sa mo lb s = Some (row_addr cat i, DP i))
  by (rewrite (pp_res_live cat DP sa mo lb s i Hl Hrow), (pp_label_at_none DP sa s i Hlab); reflexivity).
  p3_end HS HJ HKE HARc HARN Hfrs HPERM ELF HOCF AG F FL Hfin EFA LAWS fpos E88 E75 Hm Hl' Hl RC4 E70 E87 Hres
    E11n E12n E102 ltac:(rewrite sv_denot_SOff0; ewpeel; exact E403).
- (* no ':' in s: the byte at sa + toklen is the NUL, the label is the row's display pointer *)
  p3_add HS AG (YP09.mkRegion (Some 401%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))])
  ltac:(ewpeel; rewrite E401, unsigned_lit_small by lia; split; [lia|]; split; [lia|];
    split; [intros oo Hoo; lia|]; apply Forall_cons; [|apply Forall_nil];
    apply (chunk_ok_val tfibsegs _ _ (sa + Z.of_nat (colon_idx s)) 0 1 (SLit 0) 0);
    [reflexivity | change (2 ^ (8 * Z.of_N 1)) with 256; lia | cbn; lia |
     rewrite Z.add_0_r; let V0 := fresh "V0" in pose proof (HVs (colon_idx s) ltac:(lia)) as V0; rewrite Hb0 in V0; exact V0])
  ltac:(first
    [ clear - Boff T8 T15 STRb Hc1; unfold p3w, YImgTop.IMG_LO, YImgTop.IMG_TOP in *; lia
    | clear - STR0; unfold p3w in *; lia
    | clear - BS STRb Hc1 HF8r; unfold p3w in *; lia
    | clear - BFd STRb Hc1; unfold p3w in *; lia
    | clear - STR0 Hsp1; unfold p3w in *; lia ]).
  (* 0x80d08-0x80d90: the checked string byte, the check of row + 8 and its load, the out-cells; to 0x80d94 *)
  p3_run HS HJ HKE HARc HARN Hfrs HPERM ELF HOCF AG F FL fpos EFA Hm Hl' Hl HbmN E401 E102 E32n HcRA Trow SHOK.
  assert (Hres : pin_parse_res cat DP sa mo lb s = Some (row_addr cat i, DP i))
  by (rewrite (pp_res_live cat DP sa mo lb s i Hl Hrow), (pp_label_at_none DP sa s i Hlab); reflexivity).
  p3_end HS HJ HKE HARc HARN Hfrs HPERM ELF HOCF AG F FL Hfin EFA LAWS fpos E88 E75 Hm Hl' Hl RC4 E70 E87 Hres
    E11n E12n E102 ltac:(rewrite sv_denot_SOff0; ewpeel; exact E403).
Qed.
End c.

Print Assumptions pp_seg3.
