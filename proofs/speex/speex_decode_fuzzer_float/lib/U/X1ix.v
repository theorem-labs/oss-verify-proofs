(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1cc X1bk X1bj X1cf X1bu.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ik X1ii X1it.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qz X1r0 X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma firstn_upd_at : forall {X} (ws : list X) (w : X) n, (n < length ws)%nat ->
firstn (S n) (upd ws n w) = firstn n ws ++ [w].
Proof.
induction ws as [|x ws IH]; intros w n Hn; cbn in Hn; [lia|].
destruct n as [|n]; cbn [upd firstn app]; [reflexivity|]. f_equal. apply IH. lia.
Qed.

Lemma wpre_snoc : forall l ws (w : word) v, wpre l ws -> (length l < length ws)%nat -> w = wz v ->
wpre (l ++ [v]) (upd ws (length l) w).
Proof.
intros l ws w v [P L] Hl ->. unfold wpre. rewrite app_length, upd_length, map_app. cbn [length map]. split; [|lia].
rewrite Nat.add_1_r, firstn_upd_at by lia. rewrite P. reflexivity.
Qed.

Lemma firstn_upd_in : forall {X} (ws : list X) n i (w : X), (i < n)%nat -> (n <= length ws)%nat ->
firstn n (upd ws i w) = upd (firstn n ws) i w.
Proof.
induction ws as [|w0 ws IH]; intros n i w Hi Hn; cbn in Hn; [lia|].
destruct n as [|n]; [lia|]. destruct i as [|i]; cbn [upd firstn]; [reflexivity|].
f_equal. apply IH; lia.
Qed.

Lemma upd_map_wz : forall l i v, upd (map wz l) i (wz v) = map wz (upd_nat l i v).
Proof. induction l as [|x l IH]; intros [|i] v; cbn; try reflexivity. f_equal. apply IH. Qed.

Lemma wpre_upd : forall l ws (w : word) v i, wpre l ws -> (i < length l)%nat -> w = wz v ->
wpre (upd_nat l i v) (upd ws i w).
Proof.
intros l ws w v i [P L] Hi ->. unfold wpre. rewrite upd_nat_length, upd_length. split; [|exact L].
rewrite firstn_upd_in by lia. rewrite P. apply upd_map_wz.
Qed.

Lemma wpre_length : forall l ws, wpre l ws -> (length l <= length ws)%nat.
Proof. intros l ws [_ L]. exact L. Qed.

Lemma lor_small : forall a b k, 0 <= a < 2^k -> 0 <= b < 2^k -> 0 <= Z.lor a b < 2^k.
Proof.
intros a b k Ha Hb. split; [apply Z.lor_nonneg; lia|].
destruct (Z.eq_dec (Z.lor a b) 0) as [E|NE]; [rewrite E; lia|].
assert (Hk : 0 < k). { destruct (Z.lt_ge_cases 0 k); [lia|]. assert (X : 2^k <= 2^0) by (apply Z.pow_le_mono_r; lia). rewrite Z.pow_0_r in X.
assert (a = 0) by lia. assert (b = 0) by lia. subst. rewrite Z.lor_0_l in NE. lia. }
pose proof (Z.lor_nonneg a b).
apply Z.log2_lt_pow2; [lia|]. rewrite Z.log2_lor by lia.
apply Z.max_lub_lt.
- destruct (Z.eq_dec a 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
- destruct (Z.eq_dec b 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma upd_upd : forall {X} (l : list X) i (a b : X), upd (upd l i a) i b = upd l i b.
Proof. induction l as [|x l IH]; intros [|i] a b; cbn; try reflexivity. f_equal. apply IH. Qed.

Lemma zslice_cons : forall off n l, 0 <= off -> off < zlength l -> 0 < n ->
zslice off n l = znth l off :: zslice (off + 1) (n - 1) l.
Proof.
intros off n l Ho Hl Hn. replace n with (Z.of_nat (S (Z.to_nat (n - 1)))) at 1 by lia.
rewrite zslice_S by assumption. f_equal. f_equal. lia.
Qed.

Lemma zdrop_zslice : forall (l : list Z) a n k, 0 <= a -> 0 <= k <= n ->
zdrop k (zslice a n l) = zslice (a + k) (n - k) l.
Proof.
intros l a n k Ha Hk. unfold zdrop, zslice, ztake, zdrop.
destruct (Z.ltb_spec a 0); [lia|]. destruct (Z.ltb_spec (a + k) 0); [lia|].
rewrite skipn_firstn_comm, skipn_skipn. f_equal; [lia|]. f_equal. lia.
Qed.

Lemma sx32_m1 : sx32 (Z_to_bv 64 (-1)) = Z_to_bv 64 (-1).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Section PIF.
Context {RCEIL : RunCeiling}.

Variables (A Bd L Gv H lo : Z) (shdr hs : list byte) (os3 : stream_st bptr).
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (x1 : word) (segptr bosv pn : Z) (h18w h21w : word) (j0 : list byte).
Local Notation hdr := (ubytes hs).
Local Notation nseg := (znth (ubytes hs) 26).
Local Notation fl := (znth (ubytes hs) 5).
Local Notation ls := (os_lacing_storage os3).
Local Notation W := [(bv_unsigned sp - 144, bv_unsigned sp); (A, A + 408); (L, L + 4 * ls); (Gv, Gv + 8 * ls)].
Hypothesis LENH : length hs = (27 + Z.to_nat nseg)%nat.
Hypothesis Hnseg : 0 <= nseg < 256.
Hypothesis HL : length shdr = 284%nat.
Hypothesis FOK : stream_fields_ok os3.
Hypothesis Hls : os_lacing_fill os3 + (nseg - segptr) + 1 <= ls.
Hypothesis Hseg : 0 <= segptr <= nseg.
Hypothesis Hbos : bosv = 0 \/ bosv = Z.land fl 2.
Hypothesis LFILL : zlength (os_lacing os3) = os_lacing_fill os3.
Hypothesis LPK : 0 <= os_lacing_packet os3 <= os_lacing_fill os3.
Hypothesis LOK : lacing_vals_ok (os_lacing os3).
Hypothesis HA : 0 < A. Hypothesis HLv : 0 < L. Hypothesis HGv : 0 < Gv. Hypothesis HH : 0 <= H.
Hypothesis TOPL : L + 4 * ls < 2^63. Hypothesis TOPG : Gv + 8 * ls < 2^63. Hypothesis TOPH : H + Z.of_nat (length hs) < 2^63.
Hypothesis LOSP : lo + 144 <= bv_unsigned sp.
Hypothesis SPA : bv_unsigned sp <= A.

Hypothesis SEP_fL : L + 4 * ls <= lo.
Hypothesis SEP_fG : Gv + 8 * ls <= lo.
Hypothesis SEP_Hf : H + Z.of_nat (length hs) <= lo.
Hypothesis SEP_LG : L + 4 * ls <= Gv \/ Gv + 8 * ls <= L.
Hypothesis SEP_HL : H + Z.of_nat (length hs) <= L \/ L + 4 * ls <= H.
Hypothesis SEP_HG : H + Z.of_nat (length hs) <= Gv \/ Gv + 8 * ls <= H.

#[local] Set Default Proof Using "LENH Hnseg HL FOK Hls Hseg Hbos LFILL LPK LOK HA HLv HGv HH TOPL TOPG TOPH LOSP SPA SEP_fL SEP_fG SEP_Hf SEP_LG SEP_HL SEP_HG".

Local Notation FRAME m loc := (rw_cells rsegs m (bv_unsigned sp + -144)
(loc ++ [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
Local Notation LOC := [CB 8 j0; C8 (wz (ogg_page_granulepos hdr)); C8 h18w; C8 h21w; C8 (Z_to_bv 64 fl)].

Definition os_fp (f p : Z) : stream_st bptr :=
set_lacing os3 (os_lacing os3) (os_granules os3) ls f p (os_lacing_returned os3).

Definition loop3_post (i f p sv nb : Z) (lcur : list Z) (x10 wm1 x18 x19 x20 x22 x23 x27 x29 x30 x31 : word) (m : mem) : machine_state -> Prop :=
fun ms' =>
let '(lac, gran, f', p', sv') := seg_loop (zslice (27 + i) (nseg - i) hdr) (nb =? 0) f p sv in
exists (x5 x6 x7 x28 : word) m' lws' gws',
ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp x5 x6 x7 (Z_to_bv 64 A) (Z_to_bv 64 fl) x10
(Z_to_bv 64 L) (Z_to_bv 64 Gv) wm1 (Z_to_bv 64 255) (Z_to_bv 64 (H + 27 + nseg)) (Z_to_bv 64 (H + 27 + nseg)) (Z_to_bv 64 sv')
x18 x19 x20 (Z_to_bv 64 H) x22 x23 (Z_to_bv 64 pn) (Z_to_bv 64 bosv) (Z_to_bv 64 nseg) x27 x28 x29 x30 x31)
F (Z_to_bv 64 0x30ba0) fc None m' (seg_rom rsegs)
/\ munch W m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' A (stream_cells Bd L Gv shdr (os_fp f' p'))
/\ u32arr rsegs m' L lws' /\ wpre (lcur ++ lac) lws' /\ Z.of_nat (length lws') = ls
/\ u64arr rsegs m' Gv gws' /\ Z.of_nat (length gws') = ls
/\ FRAME m' LOC /\ bytes_at rsegs m' H hs.

Ltac name_hbyte k b Hb R HS :=
pose proof (bytes_at_read1 rsegs _ H hs k _ HS ltac:(lia) ltac:(lia) eq_refl) as R;
pose proof (byte_range (nth (Z.to_nat k) hs (Z_to_bv 8 0))) as Hb;
set (b := bv_unsigned (nth (Z.to_nat k) hs (Z_to_bv 8 0))) in Hb.

Lemma pi_loop3 : forall (k : nat) (i f p sv nb : Z) (lcur : list Z) (lws gws : list word) m
(x7 x10 x28 wm1 x18 x19 x20 x22 x23 x27 x29 x30 x31 : word),
Z.to_nat (nseg - i) = k -> segptr <= i < nseg -> wm1 = Z_to_bv 64 (-1) ->
f = zlength lcur -> os_lacing_fill os3 <= f -> f + (nseg - i) + 1 <= ls ->
0 <= p <= f -> -1 <= sv < f -> 0 <= nb <= 1 ->
lacing_vals_ok lcur ->
wpre lcur lws -> Z.of_nat (length lws) = ls -> Z.of_nat (length gws) = ls ->
rw_cells rsegs m A (stream_cells Bd L Gv shdr (os_fp f p)) ->
u32arr rsegs m L lws -> u64arr rsegs m Gv gws -> FRAME m LOC -> bytes_at rsegs m H hs -> mem_inv rsegs m ->
evt rsegs (loop3_post i f p sv nb lcur x10 wm1 x18 x19 x20 x22 x23 x27 x29 x30 x31 m)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp (Z_to_bv 64 f) (Z_to_bv 64 nb) x7 (Z_to_bv 64 A) (Z_to_bv 64 fl) x10
(Z_to_bv 64 L) (Z_to_bv 64 Gv) wm1 (Z_to_bv 64 255) (Z_to_bv 64 (H + 27 + nseg)) (Z_to_bv 64 (H + 27 + i)) (Z_to_bv 64 sv)
x18 x19 x20 (Z_to_bv 64 H) x22 x23 (Z_to_bv 64 pn) (Z_to_bv 64 bosv) (Z_to_bv 64 nseg) x27 x28 x29 x30 x31)
F (Z_to_bv 64 0x30b38) fc None m (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros i f p sv nb lcur lws gws m x7 x10 x28 wm1 x18 x19 x20 x22 x23 x27 x29 x30 x31 Hk Hi Hm1 Hf Hf0 Hroom Hp Hsv Hnb LOKc LPRE LLEN GLEN OS LAC GRA FR HS MI; [lia|].
pose proof FOK as sfP_; first [ sf_destruct 12%nat sfP_ as F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 | sf_fb; destruct sfP_ as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12) ]. unfold int31 in *.
unfold stream_cells, os_fp, set_lacing, wz in OS. cbn [os_body_storage os_body_fill os_body_returned os_lacing_storage os_lacing_fill os_lacing_packet os_lacing_returned
os_header_fill os_e_o_s os_b_o_s os_serialno os_pageno os_packetno os_granulepos] in OS.
pose proof (rw_cells_bound _ _ _ _ OS) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof (munch_refl W m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof HS as (HB0 & HB1 & HB). pose proof (wpre_length _ _ LPRE) as LL. unfold zlength in Hf.
name_hbyte (27 + i) v Hv Rv HS.

zstep. zstep. zstep. zstep. zstep. zstep.
rewrite !Z.shiftl_mul_pow2 by lia. change (2^2) with 4. change (2^3) with 8.
replace (Z.land nb 1) with nb by (destruct (Z.eq_dec nb 0) as [-> |]; [reflexivity| replace nb with 1 by lia; reflexivity]).

pose proof (u32arr_store_ok rsegs _ _ _ f (wa (L + 4 * f)) LAC ltac:(lia) eq_refl) as SOK.
zstep.
fold v.
pose proof (u32arr_write rsegs _ _ _ f (Z_to_bv 64 v) LAC ltac:(lia)) as LAC2. clear LAC. store_done. rename LAC2 into LAC.
pose proof (u64arr_store_ok rsegs _ _ _ f (wa (Gv + 8 * f)) GRA ltac:(lia) eq_refl) as SOK.
zstep.
pose proof (u64arr_write rsegs _ _ _ f wm1 GRA ltac:(lia)) as GRA2. clear GRA. store_done. rename GRA2 into GRA.
assert (Hf' : Z.to_nat f = length lcur) by lia.
assert (Hlor : 0 <= Z.lor v 256 < 512) by (apply (lor_small v 256 9); lia).

zstep. if_cases CNB; zify_cond CNB; rewrite ?unsigned_lit in CNB by lia.
-
idtac.

zstep. zstep. if_cases CV; zify_cond CV; rewrite ?unsigned_lit in CV by lia.
+
zstep. lstep. zstep. zstep.
zstep. if_cases CE; zify_cond CE; rewrite ?unsigned_lit in CE by lia.
*
replace (H + 27 + i + 1) with (H + 27 + (i + 1)) by lia.
eapply evt_mono.
{ eapply (IH (i + 1) (f + 1) p sv 1 (lcur ++ [v])).
all: try lazymatch goal with
| |- u32arr _ _ _ _ => exact LAC
| |- u64arr _ _ _ _ => exact GRA
| |- bytes_at _ _ _ _ => exact HS
| |- mem_inv _ _ => assumption
| |- rw_cells _ _ _ (stream_cells _ _ _ _ _) => lazymatch goal with OSx : rw_cells rsegs _ A _ |- _ => exact OSx end
| |- rw_cells _ _ _ _ => eassumption
end.
all: lazymatch goal with
| |- wpre (_ ++ _) _ => rewrite Hf'; apply wpre_snoc; [exact LPRE| lia| reflexivity]
| |- lacing_vals_ok _ => apply Forall_app; split; [exact LOKc| apply Forall_cons; [cbv beta; lia| apply Forall_nil]]
| |- _ => first [reflexivity | exact Hm1 | unfold zlength in *; rewrite ?app_length, ?upd_length; cbn [length]; lia]
end. }
cbv beta. intros ms' PO. unfold loop3_post in PO |- *.
rewrite (zslice_cons (27 + i)) by (rewrite ?zlength_ubytes; unfold zlength; lia). cbn [seg_loop].
replace (27 + i + 1) with (27 + (i + 1)) by lia. replace (nseg - i - 1) with (nseg - (i + 1)) by lia.
replace (znth hdr (27 + i)) with v by (unfold v; symmetry; apply znth_ubytes; lia).
replace (v <? 255) with false by (symmetry; apply Z.ltb_ge; lia).
replace (nb =? 0) with false by (symmetry; first [apply Z.eqb_neq; exact CNB | apply Z.eqb_eq; exact CNB]). change (1 =? 0) with false in PO. cbn iota.
destruct (seg_loop (zslice (27 + (i + 1)) (nseg - (i + 1)) hdr) false (f + 1) p sv) as [[[[lac gran] f'] p'] sv'].
first [ sf_destruct 19%nat PO as y5 y6 y7 y28 m' lws' gws' -> MU' WM' MI' OS' LAC' LP' LL' GRA' GL' FR' HS' | sf_fb; destruct PO as (y5 & y6 & y7 & y28 & m' & lws' & gws' & -> & MU' & WM' & MI' & OS' & LAC' & LP' & LL' & GRA' & GL' & FR' & HS') ].
first [ unshelve sf_eexists 7%nat; [ exact (y5) | exact (y6) | exact (y7) | exact (y28) | exact (m') | exact (lws') | exact (gws') | ] | sf_fb; exists y5, y6, y7, y28, m', lws', gws' ].
split; [reflexivity|]. split; [eapply munch_trans; [exact MU| exact MU']|]. split; [eapply wmono_trans; [exact WM| exact WM']|]. split; [exact MI'|].
split; [exact OS'|]. split; [exact LAC'|]. split; [rewrite <- app_assoc in LP'; exact LP'|]. split; [exact LL'|].
split; [exact GRA'|]. split; [exact GL'|]. split; [exact FR'| exact HS'].
*
apply evt_done. unfold loop3_post.
rewrite (zslice_cons (27 + i)) by (rewrite ?zlength_ubytes; unfold zlength; lia).
replace (nseg - i - 1) with 0 by lia. rewrite zslice_0. cbn [seg_loop].
replace (znth hdr (27 + i)) with v by (unfold v; symmetry; apply znth_ubytes; (clear - CE Hf' LL GB Hi Hk gws lws lcur f i k Hseg HL LENH segptr hs shdr H A Hroom Hf SEP_HG SEP_HL SEP_LG os3 Gv L; lia)).
replace (v <? 255) with false by (symmetry; apply Z.ltb_ge; lia).
replace (nb =? 0) with false by (symmetry; first [apply Z.eqb_neq; exact CNB | apply Z.eqb_eq; exact CNB]). cbn iota.
replace (H + 27 + i + 1) with (H + 27 + nseg) by lia.
sf_eexists 4%nat. lazymatch goal with |- context [MS _ _ _ _ _ ?mx _ = _] => exists mx end.
exists (upd lws (Z.to_nat f) (Z_to_bv 64 v)), (upd gws (Z.to_nat f) wm1).
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
split; [lazymatch goal with OSx : rw_cells rsegs _ A _ |- _ => exact OSx end|].
split; [exact LAC|]. split; [rewrite Hf'; apply wpre_snoc; [exact LPRE| lia| reflexivity]|]. split; [rewrite upd_length; exact LLEN|].
split; [exact GRA|]. split; [rewrite upd_length; exact GLEN|].
split; [exact FR| exact HS].
+
zstep. lstep. zstep. zstep. lstep. zstep. zstep.
zstep. if_cases CE; zify_cond CE; rewrite ?unsigned_lit in CE by lia.
* replace (H + 27 + i + 1) with (H + 27 + (i + 1)) by lia.
eapply evt_mono.
{ eapply (IH (i + 1) (f + 1) (f + 1) f 1 (lcur ++ [v])).
all: try lazymatch goal with
| |- u32arr _ _ _ _ => exact LAC
| |- u64arr _ _ _ _ => exact GRA
| |- bytes_at _ _ _ _ => exact HS
| |- mem_inv _ _ => assumption
| |- rw_cells _ _ _ (stream_cells _ _ _ _ _) => lazymatch goal with OSx : rw_cells rsegs _ A _ |- _ => exact OSx end
| |- rw_cells _ _ _ _ => eassumption
end.
all: lazymatch goal with
| |- wpre (_ ++ _) _ => rewrite Hf'; apply wpre_snoc; [exact LPRE| lia| reflexivity]
| |- lacing_vals_ok _ => apply Forall_app; split; [exact LOKc| apply Forall_cons; [cbv beta; lia| apply Forall_nil]]
| |- _ => first [reflexivity | exact Hm1 | unfold zlength in *; rewrite ?app_length, ?upd_length; cbn [length]; lia]
end. }
cbv beta. intros ms' PO. unfold loop3_post in PO |- *.
rewrite (zslice_cons (27 + i)) by (rewrite ?zlength_ubytes; unfold zlength; lia). cbn [seg_loop].
replace (27 + i + 1) with (27 + (i + 1)) by lia. replace (nseg - i - 1) with (nseg - (i + 1)) by lia.
replace (znth hdr (27 + i)) with v by (unfold v; symmetry; apply znth_ubytes; (clear - Hf' LL GB Hroom Hf Hi Hk gws lws lcur f i k SEP_HG SEP_HL SEP_LG Hseg HL LENH segptr os3 hs shdr H Gv L A; lia)).
replace (v <? 255) with true by (symmetry; apply Z.ltb_lt; lia).
replace (nb =? 0) with false by (symmetry; first [apply Z.eqb_neq; exact CNB | apply Z.eqb_eq; exact CNB]). change (1 =? 0) with false in PO. cbn iota.
destruct (seg_loop (zslice (27 + (i + 1)) (nseg - (i + 1)) hdr) false (f + 1) (f + 1) f) as [[[[lac gran] f'] p'] sv'].
first [ sf_destruct 19%nat PO as y5 y6 y7 y28 m' lws' gws' -> MU' WM' MI' OS' LAC' LP' LL' GRA' GL' FR' HS' | sf_fb; destruct PO as (y5 & y6 & y7 & y28 & m' & lws' & gws' & -> & MU' & WM' & MI' & OS' & LAC' & LP' & LL' & GRA' & GL' & FR' & HS') ].
first [ unshelve sf_eexists 7%nat; [ exact (y5) | exact (y6) | exact (y7) | exact (y28) | exact (m') | exact (lws') | exact (gws') | ] | sf_fb; exists y5, y6, y7, y28, m', lws', gws' ].
split; [reflexivity|]. split; [eapply munch_trans; [exact MU| exact MU']|]. split; [eapply wmono_trans; [exact WM| exact WM']|]. split; [exact MI'|].
split; [exact OS'|]. split; [exact LAC'|]. split; [rewrite <- app_assoc in LP'; exact LP'|]. split; [exact LL'|].
split; [exact GRA'|]. split; [exact GL'|]. split; [exact FR'| exact HS'].
* apply evt_done. unfold loop3_post.
rewrite (zslice_cons (27 + i)) by (rewrite ?zlength_ubytes; unfold zlength; lia).
replace (nseg - i - 1) with 0 by lia. rewrite zslice_0. cbn [seg_loop].
replace (znth hdr (27 + i)) with v by (unfold v; symmetry; apply znth_ubytes; (clear - CE Hf' LL GB Hi Hk gws lws lcur f i k Hseg HL LENH segptr hs shdr H A Hroom Hf SEP_HG SEP_HL SEP_LG os3 Gv L; lia)).
replace (v <? 255) with true by (symmetry; apply Z.ltb_lt; lia).
replace (nb =? 0) with false by (symmetry; first [apply Z.eqb_neq; exact CNB | apply Z.eqb_eq; exact CNB]). cbn iota.
replace (H + 27 + i + 1) with (H + 27 + nseg) by lia.
sf_eexists 4%nat. lazymatch goal with |- context [MS _ _ _ _ _ ?mx _ = _] => exists mx end.
exists (upd lws (Z.to_nat f) (Z_to_bv 64 v)), (upd gws (Z.to_nat f) wm1).
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
split; [lazymatch goal with OSx : rw_cells rsegs _ A _ |- _ => exact OSx end|].
split; [exact LAC|]. split; [rewrite Hf'; apply wpre_snoc; [exact LPRE| lia| reflexivity]|]. split; [rewrite upd_length; exact LLEN|].
split; [exact GRA|]. split; [rewrite upd_length; exact GLEN|].
split; [exact FR| exact HS].
-
zstep. zstep. zstep. rewrite !Z.shiftl_mul_pow2 by lia. change (2^2) with 4.
pose proof (u32arr_read rsegs _ L _ f (Z_to_bv 64 v) (wa (L + 4 * f)) LAC ltac:(rewrite nth_error_upd_same by lia; reflexivity) ltac:(lia) eq_refl) as RD.
zstep. rewrite (sx32_lit v) by (unfold int31; lia).
zstep.
pose proof (u32arr_store_ok rsegs _ _ _ f (wa (L + 4 * f)) LAC ltac:(rewrite upd_length; lia) eq_refl) as SOK2.
zstep.
pose proof (u32arr_write rsegs _ _ _ f (Z_to_bv 64 (Z.lor v 256)) LAC ltac:(rewrite upd_length; lia)) as LAC2. clear LAC.
rewrite upd_upd in LAC2. store_done. rename LAC2 into LAC.

zstep. zstep. if_cases CV; zify_cond CV; rewrite ?unsigned_lit in CV by lia.
+
zstep. lstep. zstep. zstep.
zstep. if_cases CE; zify_cond CE; rewrite ?unsigned_lit in CE by lia.
*
replace (H + 27 + i + 1) with (H + 27 + (i + 1)) by lia.
eapply evt_mono.
{ eapply (IH (i + 1) (f + 1) p sv 1 (lcur ++ [(Z.lor v 256)])).
all: try lazymatch goal with
| |- u32arr _ _ _ _ => exact LAC
| |- u64arr _ _ _ _ => exact GRA
| |- bytes_at _ _ _ _ => exact HS
| |- mem_inv _ _ => assumption
| |- rw_cells _ _ _ (stream_cells _ _ _ _ _) => lazymatch goal with OSx : rw_cells rsegs _ A _ |- _ => exact OSx end
| |- rw_cells _ _ _ _ => eassumption
end.
all: lazymatch goal with
| |- wpre (_ ++ _) _ => rewrite Hf'; apply wpre_snoc; [exact LPRE| lia| reflexivity]
| |- lacing_vals_ok _ => apply Forall_app; split; [exact LOKc| apply Forall_cons; [cbv beta; lia| apply Forall_nil]]
| |- _ => first [reflexivity | exact Hm1 | unfold zlength in *; rewrite ?app_length, ?upd_length; cbn [length]; lia]
end. }
cbv beta. intros ms' PO. unfold loop3_post in PO |- *.
rewrite (zslice_cons (27 + i)) by (rewrite ?zlength_ubytes; unfold zlength; lia). cbn [seg_loop].
replace (27 + i + 1) with (27 + (i + 1)) by lia. replace (nseg - i - 1) with (nseg - (i + 1)) by lia.
replace (znth hdr (27 + i)) with v by (unfold v; symmetry; apply znth_ubytes; lia).
replace (v <? 255) with false by (symmetry; apply Z.ltb_ge; lia).
replace (nb =? 0) with true by (symmetry; first [apply Z.eqb_neq; exact CNB | apply Z.eqb_eq; exact CNB]). change (1 =? 0) with false in PO. cbn iota.
destruct (seg_loop (zslice (27 + (i + 1)) (nseg - (i + 1)) hdr) false (f + 1) p sv) as [[[[lac gran] f'] p'] sv'].
first [ sf_destruct 19%nat PO as y5 y6 y7 y28 m' lws' gws' -> MU' WM' MI' OS' LAC' LP' LL' GRA' GL' FR' HS' | sf_fb; destruct PO as (y5 & y6 & y7 & y28 & m' & lws' & gws' & -> & MU' & WM' & MI' & OS' & LAC' & LP' & LL' & GRA' & GL' & FR' & HS') ].
first [ unshelve sf_eexists 7%nat; [ exact (y5) | exact (y6) | exact (y7) | exact (y28) | exact (m') | exact (lws') | exact (gws') | ] | sf_fb; exists y5, y6, y7, y28, m', lws', gws' ].
split; [reflexivity|]. split; [eapply munch_trans; [exact MU| exact MU']|]. split; [eapply wmono_trans; [exact WM| exact WM']|]. split; [exact MI'|].
split; [exact OS'|]. split; [exact LAC'|]. split; [rewrite <- app_assoc in LP'; exact LP'|]. split; [exact LL'|].
split; [exact GRA'|]. split; [exact GL'|]. split; [exact FR'| exact HS'].
*
apply evt_done. unfold loop3_post.
rewrite (zslice_cons (27 + i)) by (rewrite ?zlength_ubytes; unfold zlength; (clear - CE Hf' LL GB Hi Hk gws lws lcur f i k Hseg HL LENH segptr hs shdr H A Hroom Hf SEP_HG SEP_HL SEP_LG os3 Gv L; lia)).
replace (nseg - i - 1) with 0 by lia. rewrite zslice_0. cbn [seg_loop].
replace (znth hdr (27 + i)) with v by (unfold v; symmetry; apply znth_ubytes; lia).
replace (v <? 255) with false by (symmetry; apply Z.ltb_ge; lia).
replace (nb =? 0) with true by (symmetry; first [apply Z.eqb_neq; exact CNB | apply Z.eqb_eq; exact CNB]). cbn iota.
replace (H + 27 + i + 1) with (H + 27 + nseg) by lia.
sf_eexists 4%nat. lazymatch goal with |- context [MS _ _ _ _ _ ?mx _ = _] => exists mx end.
exists (upd lws (Z.to_nat f) (Z_to_bv 64 (Z.lor v 256))), (upd gws (Z.to_nat f) wm1).
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
split; [lazymatch goal with OSx : rw_cells rsegs _ A _ |- _ => exact OSx end|].
split; [exact LAC|]. split; [rewrite Hf'; apply wpre_snoc; [exact LPRE| lia| reflexivity]|]. split; [rewrite upd_length; exact LLEN|].
split; [exact GRA|]. split; [rewrite upd_length; exact GLEN|].
split; [exact FR| exact HS].
+
zstep. lstep. zstep. zstep. lstep. zstep. zstep.
zstep. if_cases CE; zify_cond CE; rewrite ?unsigned_lit in CE by lia.
* replace (H + 27 + i + 1) with (H + 27 + (i + 1)) by lia.
eapply evt_mono.
{ eapply (IH (i + 1) (f + 1) (f + 1) f 1 (lcur ++ [(Z.lor v 256)])).
all: try lazymatch goal with
| |- u32arr _ _ _ _ => exact LAC
| |- u64arr _ _ _ _ => exact GRA
| |- bytes_at _ _ _ _ => exact HS
| |- mem_inv _ _ => assumption
| |- rw_cells _ _ _ (stream_cells _ _ _ _ _) => lazymatch goal with OSx : rw_cells rsegs _ A _ |- _ => exact OSx end
| |- rw_cells _ _ _ _ => eassumption
end.
all: lazymatch goal with
| |- wpre (_ ++ _) _ => rewrite Hf'; apply wpre_snoc; [exact LPRE| (clear - Hf' LL GB LLEN Hroom Hf Hi Hk gws lws lcur f i k SEP_HG SEP_HL SEP_LG HL LENH segptr os3 hs shdr H Gv L A; lia)| reflexivity]
| |- lacing_vals_ok _ => apply Forall_app; split; [exact LOKc| apply Forall_cons; [cbv beta; (clear - Hlor v; lia)| apply Forall_nil]]
| |- _ => first [reflexivity | exact Hm1 | unfold zlength in *; rewrite ?app_length, ?upd_length; cbn [length]; (clear - CE Hf' Hi Hk gws lws lcur f i k segptr hs H LL Hf Hf0 os3 Hroom Hp p LLEN GLEN; lia)]
end. }
cbv beta. intros ms' PO. unfold loop3_post in PO |- *.
rewrite (zslice_cons (27 + i)) by (rewrite ?zlength_ubytes; unfold zlength; lia). cbn [seg_loop].
replace (27 + i + 1) with (27 + (i + 1)) by lia. replace (nseg - i - 1) with (nseg - (i + 1)) by lia.
replace (znth hdr (27 + i)) with v by (unfold v; symmetry; apply znth_ubytes; (clear - Hf' LL GB Hroom Hf Hi Hk gws lws lcur f i k SEP_HG SEP_HL SEP_LG Hseg HL LENH segptr os3 hs shdr H Gv L A; lia)).
replace (v <? 255) with true by (symmetry; apply Z.ltb_lt; lia).
replace (nb =? 0) with true by (symmetry; first [apply Z.eqb_neq; exact CNB | apply Z.eqb_eq; exact CNB]). change (1 =? 0) with false in PO. cbn iota.
destruct (seg_loop (zslice (27 + (i + 1)) (nseg - (i + 1)) hdr) false (f + 1) (f + 1) f) as [[[[lac gran] f'] p'] sv'].
first [ sf_destruct 19%nat PO as y5 y6 y7 y28 m' lws' gws' -> MU' WM' MI' OS' LAC' LP' LL' GRA' GL' FR' HS' | sf_fb; destruct PO as (y5 & y6 & y7 & y28 & m' & lws' & gws' & -> & MU' & WM' & MI' & OS' & LAC' & LP' & LL' & GRA' & GL' & FR' & HS') ].
first [ unshelve sf_eexists 7%nat; [ exact (y5) | exact (y6) | exact (y7) | exact (y28) | exact (m') | exact (lws') | exact (gws') | ] | sf_fb; exists y5, y6, y7, y28, m', lws', gws' ].
split; [reflexivity|]. split; [eapply munch_trans; [exact MU| exact MU']|]. split; [eapply wmono_trans; [exact WM| exact WM']|]. split; [exact MI'|].
split; [exact OS'|]. split; [exact LAC'|]. split; [rewrite <- app_assoc in LP'; exact LP'|]. split; [exact LL'|].
split; [exact GRA'|]. split; [exact GL'|]. split; [exact FR'| exact HS'].
* apply evt_done. unfold loop3_post.
rewrite (zslice_cons (27 + i)) by (rewrite ?zlength_ubytes; unfold zlength; lia).
replace (nseg - i - 1) with 0 by lia. rewrite zslice_0. cbn [seg_loop].
replace (znth hdr (27 + i)) with v by (unfold v; symmetry; apply znth_ubytes; lia).
replace (v <? 255) with true by (symmetry; apply Z.ltb_lt; lia).
replace (nb =? 0) with true by (symmetry; first [apply Z.eqb_neq; exact CNB | apply Z.eqb_eq; exact CNB]). cbn iota.
replace (H + 27 + i + 1) with (H + 27 + nseg) by lia.
sf_eexists 4%nat. lazymatch goal with |- context [MS _ _ _ _ _ ?mx _ = _] => exists mx end.
exists (upd lws (Z.to_nat f) (Z_to_bv 64 (Z.lor v 256))), (upd gws (Z.to_nat f) wm1).
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
split; [lazymatch goal with OSx : rw_cells rsegs _ A _ |- _ => exact OSx end|].
split; [exact LAC|]. split; [rewrite Hf'; apply wpre_snoc; [exact LPRE| lia| reflexivity]|]. split; [rewrite upd_length; exact LLEN|].
split; [exact GRA|]. split; [rewrite upd_length; exact GLEN|].
split; [exact FR| exact HS].
Qed.
End PIF.
