(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1cc X1bk X1bj X1cf X1bu.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ik X1ii X1it X1ix.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qz X1r0 X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma sx32_small : forall v, -2^31 <= v < 2^31 -> sx32 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof.
intros v Hv. unfold sx32. f_equal. rewrite Z_to_bv_unsigned.
unfold bv_swrap, bv_wrap. change (bv_modulus 64) with (2^64). change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
destruct (Z.lt_ge_cases v 0).
- replace (v mod 2^64) with (v + 2^64) by (apply Z.mod_unique with (q := -1); lia).
replace (v + 2^64 + 2^31) with (v + 2^31 + 2^32 * 2^32) by lia. rewrite Z_mod_plus_full, Z.mod_small; lia.
- rewrite (Z.mod_small v) by lia. rewrite Z.mod_small; lia.
Qed.

Lemma shl32_shr32 : forall x, 0 <= x < 2^32 -> Z.land (x * 2^32) (2^64 - 1) / 2^32 = x.
Proof.
intros x Hx. change (2^64 - 1) with (Z.ones 64). rewrite Z.land_ones by lia.
rewrite Z.mod_small by (split; [lia|]; change (2^64) with (2^32 * 2^32); nia). rewrite Z.div_mul by lia. reflexivity.
Qed.

Lemma swrap32_sextw : forall x, -2^31 <= x < 2^31 -> bv_swrap 32 (Z.land x 18446744073709551615 + 0) = x.
Proof.
intros x Hx. rewrite Z.add_0_r, land_ones64.
unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
destruct (Z.lt_ge_cases x 0).
- replace (x mod 2^64) with (x + 2^64) by (apply Z.mod_unique with (q := -1); lia).
replace (x + 2^64 + 2^31) with (x + 2^31 + 2^32 * 2^32) by lia. rewrite Z_mod_plus_full, Z.mod_small; lia.
- rewrite (Z.mod_small x) by lia. rewrite Z.mod_small; lia.
Qed.

Lemma seg_loop_vals512 : forall vals bos fill packet saved lac gran f p s,
Forall (fun v => 0 <= v < 256) vals ->
seg_loop vals bos fill packet saved = (lac, gran, f, p, s) ->
Forall (fun x => 0 <= x < 512) lac.
Proof.
induction vals as [|v vals IH]; intros bos fill packet saved lac gran f p s Hb E; cbn [seg_loop] in E.
- inversion E; subst. constructor.
- inversion Hb as [|v' vals' Hv Hvals]; subst v' vals'.
destruct (seg_loop vals false (fill + 1) (if v <? 255 then fill + 1 else packet) (if v <? 255 then fill else saved))
as [[[[lac' gran'] f'] p'] s'] eqn:E'.
injection E as E1 E2 E3 E4 E5. subst lac gran f p s.
constructor; [| eapply IH; [exact Hvals| exact E']].
destruct bos; [apply (lor_small v 256 9); lia| lia].
Qed.

Lemma zlength_zslice : forall off n (l : list Z), 0 <= off -> 0 <= n -> off + n <= zlength l -> zlength (zslice off n l) = n.
Proof.
intros off n l Ho Hn Hl. unfold zslice, ztake, zdrop, zlength in *. destruct (Z.ltb_spec off 0); [lia|].
rewrite firstn_length_le by (rewrite skipn_length; lia). lia.
Qed.

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

Hypothesis Hpneq : pn = ogg_page_pageno hdr.
#[local] Set Default Proof Using "LENH Hnseg HL FOK Hls Hseg Hbos LFILL LPK LOK HA HLv HGv HH TOPL TOPG TOPH LOSP SPA SEP_fL SEP_fG SEP_Hf SEP_LG SEP_HL SEP_HG Hpneq".

Local Notation FRAME m loc := (rw_cells rsegs m (bv_unsigned sp + -144)
(loc ++ [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
Local Notation LOC := [CB 8 j0; C8 (wz (ogg_page_granulepos hdr)); C8 h18w; C8 h21w; C8 (Z_to_bv 64 fl)].

Local Notation pi_loop3' := (X1ix.pi_loop3 A Bd L Gv H lo shdr hs os3 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc x1 segptr bosv pn h18w h21w j0 LENH Hnseg HL FOK Hls Hseg Hbos LFILL LPK LOK HA HLv HGv HH TOPL TOPG TOPH LOSP SPA SEP_fL SEP_fG SEP_Hf SEP_LG SEP_HL SEP_HG).
Local Notation os_fp := (X1ix.os_fp os3).

Local Notation osF := (pagein_segments os3 hdr bosv segptr).

Definition final_post (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m' lws' gws',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch W m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' A (stream_cells Bd L Gv shdr osF)
/\ u32arr rsegs m' L lws' /\ wpre (os_lacing osF) lws' /\ Z.of_nat (length lws') = ls
/\ u64arr rsegs m' Gv gws' /\ Z.of_nat (length gws') = ls
/\ stk rsegs m' lo (bv_unsigned sp) /\ bytes_at rsegs m' H hs.

Lemma pi_tail : forall m0 m (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x18 x19 x20 x22 x23 x27 x29 x30 x31 : word)
(lac gran : list Z) (f1 p1 sv : Z) (lws1 gws1 : list word),
seg_loop (zdrop segptr (lacing_of hdr)) (negb (bosv =? 0)) (os_lacing_fill os3) (os_lacing_packet os3) (-1) = (lac, gran, f1, p1, sv) ->
let lacA := os_lacing os3 ++ lac in
wpre lacA lws1 -> Z.of_nat (length lws1) = ls -> Z.of_nat (length gws1) = ls ->
f1 = zlength lacA -> 0 <= p1 <= f1 -> f1 <= ls -> lacing_vals_ok lacA -> 0 <= pn < 2^32 ->
munch W m0 m -> wmono rsegs m0 m ->
rw_cells rsegs m A (stream_cells Bd L Gv shdr (os_fp f1 p1)) ->
u32arr rsegs m L lws1 -> u64arr rsegs m Gv gws1 -> FRAME m LOC -> bytes_at rsegs m H hs -> mem_inv rsegs m ->
stk rsegs m lo (bv_unsigned sp + -144) ->
evt rsegs (final_post m0)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp x5 x6 x7 (Z_to_bv 64 A) (Z_to_bv 64 fl) (Z_to_bv 64 (Z.land fl 4))
x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 (Z_to_bv 64 H) x22 x23 (Z_to_bv 64 pn) (Z_to_bv 64 bosv) (Z_to_bv 64 nseg) x27 x28 x29 x30 x31)
F (Z_to_bv 64 0x30bc0) fc None m (seg_rom rsegs)).
Proof.
intros until gws1. intros SEG. cbv zeta. intros LPRE LLEN GLEN Hf1 Hp1 Hfl1 LOK1 Hpn MU WM OS LAC GRA FR HS MI ST.
pose proof FOK as sfP_; first [ sf_destruct 12%nat sfP_ as F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 | sf_fb; destruct sfP_ as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12) ]. unfold int31 in *.
pose proof (rw_cells_bound _ _ _ _ OS) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof HS as (HB0 & HB1 & HB). pose proof (wpre_length _ _ LPRE) as LL. unfold zlength in Hf1.
pose proof (byte_range (nth (Z.to_nat 5) hs (Z_to_bv 8 0))) as Hfl. rewrite <- (znth_ubytes hs 5) in Hfl by lia.
pose proof (Z_land_range fl 4 ltac:(lia) ltac:(lia)) as Heos.
unfold stream_cells, X1ix.os_fp, set_lacing, wz in OS. cbn [os_body_storage os_body_fill os_body_returned os_lacing_storage os_lacing_fill os_lacing_packet os_lacing_returned
os_header_fill os_e_o_s os_b_o_s os_serialno os_pageno os_packetno os_granulepos] in OS.

zstep. if_cases CEOS; zify_cond CEOS; rewrite ?unsigned_lit in CEOS by lia.
-

zstep. zstep. lstep. zstep.
zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
cbn [app] in FR. release_frame FR ST (bv_unsigned sp).
zstep. zstep.
apply evt_done. unfold final_post.
sf_eexists 14%nat. lazymatch goal with |- context [MS _ _ _ _ _ ?mx _ = _] => exists mx end.
exists lws1, gws1.
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
unfold pagein_segments. rewrite SEG.
replace (Z.land fl 4 =? 0) with true by (symmetry; first [apply Z.eqb_eq; exact CEOS | apply Z.eqb_neq; exact CEOS]). cbn [negb].
unfold set_lacing, set_tail, stream_cells, wz. cbn [os_body_storage os_body_fill os_body_returned os_lacing_storage os_lacing_fill os_lacing_packet os_lacing_returned
os_header_fill os_e_o_s os_b_o_s os_serialno os_pageno os_packetno os_granulepos os_lacing os_granules].
rewrite <- Hpneq.
split; [lazymatch goal with OSx : rw_cells rsegs _ A _ |- _ => exact OSx end|].
split; [exact LAC|]. split; [exact LPRE|]. split; [first [exact LLEN | rewrite upd_length; exact LLEN]|].
split; [exact GRA|]. split; [exact GLEN|].
split; [exact ST| exact HS].
-
zstep. zstep. lstep.
zstep. if_cases CF; zify_cond CF.
+
assert (Hf1le : f1 <= 0) by (destruct (Z.ltb_spec 0 f1); destruct (Z.ltb_spec f1 9223372036854775808); cbn in CF; try discriminate; lia).

zstep. zstep. lstep. zstep.
zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
cbn [app] in FR. release_frame FR ST (bv_unsigned sp).
zstep. zstep.
apply evt_done. unfold final_post.
sf_eexists 14%nat. lazymatch goal with |- context [MS _ _ _ _ _ ?mx _ = _] => exists mx end.
exists lws1, gws1.
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
unfold pagein_segments. rewrite SEG.
replace (Z.land fl 4 =? 0) with false by (symmetry; first [apply Z.eqb_eq; exact CEOS | apply Z.eqb_neq; exact CEOS]). cbn [negb].
first [ replace (0 <? f1) with false by (symmetry; apply Z.ltb_ge; lia) | replace (0 <? f1) with true by (symmetry; apply Z.ltb_lt; lia) ]. cbn iota.
unfold set_lacing, set_tail, stream_cells, wz. cbn [os_body_storage os_body_fill os_body_returned os_lacing_storage os_lacing_fill os_lacing_packet os_lacing_returned
os_header_fill os_e_o_s os_b_o_s os_serialno os_pageno os_packetno os_granulepos os_lacing os_granules].
rewrite <- Hpneq.
split; [lazymatch goal with OSx : rw_cells rsegs _ A _ |- _ => exact OSx end|].
split; [exact LAC|]. split; [exact LPRE|]. split; [first [exact LLEN | rewrite upd_length; exact LLEN]|].
split; [exact GRA|]. split; [exact GLEN|].
split; [exact ST| exact HS].
+
pose proof (Forall_znth _ _ (f1 - 1) LOK1 ltac:(cbv beta; lia)) as Rv. cbv beta in Rv.
zstep. zstep. zstep. rewrite !Z.shiftl_mul_pow2 by lia. change (2^2) with 4.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
pose proof (u32_read mx L _ lws1 (f1 - 1) (wa (L + f1 * 4 + -4)) LAC LPRE ltac:(lia) ltac:(lia) ltac:(f_equal; lia)) as RD end.
zstep. unfold wz. rewrite (sx32_lit (znth (os_lacing os3 ++ lac) (f1 - 1))) by (unfold int31; lia).
zstep.
pose proof (u32arr_store_ok rsegs _ _ _ (f1 - 1) (wa (L + f1 * 4 + -4)) LAC ltac:(lia) ltac:(f_equal; lia)) as SOK.
zstep.
replace (Z_to_bv 64 (L + f1 * 4 + -4)) with (wa (L + 4 * (f1 - 1))) by (unfold wa; f_equal; lia).
pose proof (u32arr_write rsegs _ _ _ (f1 - 1) (Z_to_bv 64 (Z.lor (znth (os_lacing os3 ++ lac) (f1 - 1)) 512)) LAC ltac:(lia)) as LAC2. clear LAC.
store_done. rename LAC2 into LAC.

zstep. zstep. lstep. zstep.
zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
cbn [app] in FR. release_frame FR ST (bv_unsigned sp).
zstep. zstep.
apply evt_done. unfold final_post.
sf_eexists 14%nat. lazymatch goal with |- context [MS _ _ _ _ _ ?mx _ = _] => exists mx end.
exists (upd lws1 (Z.to_nat (f1 - 1)) (Z_to_bv 64 (Z.lor (znth (os_lacing os3 ++ lac) (f1 - 1)) 512))), gws1.
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
unfold pagein_segments. rewrite SEG.
replace (Z.land fl 4 =? 0) with false by (symmetry; first [apply Z.eqb_eq; exact CEOS | apply Z.eqb_neq; exact CEOS]). cbn [negb].
first [ replace (0 <? f1) with false by (symmetry; apply Z.ltb_ge; lia) | replace (0 <? f1) with true by (symmetry; apply Z.ltb_lt; lia) ]. cbn iota.
unfold set_lacing, set_tail, stream_cells, wz. cbn [os_body_storage os_body_fill os_body_returned os_lacing_storage os_lacing_fill os_lacing_packet os_lacing_returned
os_header_fill os_e_o_s os_b_o_s os_serialno os_pageno os_packetno os_granulepos os_lacing os_granules].
rewrite <- Hpneq.
split; [lazymatch goal with OSx : rw_cells rsegs _ A _ |- _ => exact OSx end|].
split; [exact LAC|]. split; [unfold zupd; replace (f1 - 1 <? 0) with false by (symmetry; apply Z.ltb_ge; lia); apply wpre_upd; [exact LPRE| unfold zlength in *; lia| reflexivity]|]. split; [first [exact LLEN | rewrite upd_length; exact LLEN]|].
split; [exact GRA|]. split; [exact GLEN|].
split; [exact ST| exact HS].
Qed.

Lemma pi_final : forall m (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x18 x19 x20 x22 x27 x29 x30 x31 : word) (lws gws : list word),
wpre (os_lacing os3) lws -> Z.of_nat (length lws) = ls -> Z.of_nat (length gws) = ls ->
0 <= pn < 2^32 ->
rw_cells rsegs m A (stream_cells Bd L Gv shdr os3) ->
u32arr rsegs m L lws -> u64arr rsegs m Gv gws -> FRAME m LOC -> bytes_at rsegs m H hs -> mem_inv rsegs m ->
stk rsegs m lo (bv_unsigned sp + -144) ->
evt rsegs (final_post m)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp x5 x6 x7 (Z_to_bv 64 A) (Z_to_bv 64 fl) x10
x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 (Z_to_bv 64 H) x22 (Z_to_bv 64 segptr) (Z_to_bv 64 pn) (Z_to_bv 64 bosv) (Z_to_bv 64 nseg) x27 x28 x29 x30 x31)
F (Z_to_bv 64 0x30afc) fc None m (seg_rom rsegs)).
Proof.
intros until gws. intros LPRE LLEN GLEN Hpn OS LAC GRA FR HS MI ST.
pose proof FOK as sfP_; first [ sf_destruct 12%nat sfP_ as F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 | sf_fb; destruct sfP_ as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12) ]. unfold int31 in *.
pose proof (rw_cells_bound _ _ _ _ OS) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof (munch_refl W m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof HS as (HB0 & HB1 & HB). pose proof (wpre_length _ _ LPRE) as LL. unfold zlength in LFILL.
pose proof (byte_range (nth (Z.to_nat 5) hs (Z_to_bv 8 0))) as Hfl. rewrite <- (znth_ubytes hs 5) in Hfl by lia.
assert (Hbv : 0 <= bosv < 2^64) by (destruct Hbos as [-> | ->]; [lia| apply Z_land_range; lia]).
unfold stream_cells, wz in OS.

zstep. zstep. if_cases CL; zify_cond CL; rewrite ?zb_signed_small, ?unsigned_lit in CL by lia.
-
assert (Esp : segptr = nseg) by lia.
assert (SEG0 : seg_loop (zdrop segptr (lacing_of hdr)) (negb (bosv =? 0)) (os_lacing_fill os3) (os_lacing_packet os3) (-1)
= ([], [], os_lacing_fill os3, os_lacing_packet os3, -1)).
{ unfold lacing_of. rewrite zdrop_zslice by lia. rewrite Esp, Z.sub_diag, zslice_0. reflexivity. }
eapply (pi_tail m m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ [] [] (os_lacing_fill os3) (os_lacing_packet os3) (-1) lws gws SEG0);
cbv zeta; rewrite ?app_nil_r; try eassumption; try lia.
all: first [ unfold zlength in *; lia
| apply munch_refl | apply wmono_refl
| exact OS ].
-
zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
rewrite Z.shiftr_shiftl_l, Z.sub_diag, Z.shiftl_0_r by lia.
replace (nseg + H + 27) with (H + 27 + nseg) by lia. replace (segptr + H + 27) with (H + 27 + segptr) by lia.
set (nb := Z.b2z (bosv <? 1)).
assert (Enb : (nb =? 0) = negb (bosv =? 0)) by (subst nb; destruct (Z.ltb_spec bosv 1); destruct (Z.eqb_spec bosv 0); cbn; lia || reflexivity).
eapply evt_cut.
{ eapply (pi_loop3' (Z.to_nat (nseg - segptr)) segptr (os_lacing_fill os3) (os_lacing_packet os3) (-1) nb (os_lacing os3) lws gws);
try eassumption; try reflexivity; try lia.
all: first [ subst nb; destruct (bosv <? 1); cbn; lia
| unfold zlength in *; lia
| exact OS ]. }
cbv beta. intros ms' PO. unfold X1ix.loop3_post in PO.
destruct (seg_loop (zslice (27 + segptr) (nseg - segptr) hdr) (nb =? 0) (os_lacing_fill os3) (os_lacing_packet os3) (-1))
as [[[[lac gran] f'] p'] sv'] eqn:SEG.
first [ sf_destruct 19%nat PO as y5 y6 y7 y28 m2 lws2 gws2 -> MU2 WM2 MI2 OS2 LAC2 LP2 LL2 GRA2 GL2 FR2 HS2 | sf_fb; destruct PO as (y5 & y6 & y7 & y28 & m2 & lws2 & gws2 & -> & MU2 & WM2 & MI2 & OS2 & LAC2 & LP2 & LL2 & GRA2 & GL2 & FR2 & HS2) ].
pose proof (stk_transport_disjoint rsegs _ m m2 lo (bv_unsigned sp + -144) ST MU2 WM2 ltac:(cbn [disjoint_from]; lia)) as ST2. clear ST.

assert (HV : Forall (fun v => 0 <= v < 256) (zslice (27 + segptr) (nseg - segptr) hdr)).
{ apply (bytes_ok_zslice (27 + segptr) (nseg - segptr) hdr). apply ubytes_ok. }
pose proof (seg_loop_spec _ _ (os_lacing_fill os3) (os_lacing_packet os3) _ _ _ _ _ _ HV ltac:(lia) SEG) as sfP_; first [ sf_destruct 6%nat sfP_ as SL1 SL2 SL3 SL4 SL5 SL6 | sf_fb; destruct sfP_ as (SL1 & SL2 & SL3 & SL4 & SL5 & SL6) ].
pose proof (seg_loop_vals512 _ _ _ _ _ _ _ _ _ _ HV SEG) as SLV.
rewrite zlength_zslice in SL1, SL2, SL3 by (rewrite ?zlength_ubytes; unfold zlength; (clear - gws2 lws2 Enb nb LL gws lws Hseg HL LENH bosv segptr os3 hs shdr Gv L Bd CL Hbv F6 SEP_HG SEP_HL SEP_LG LPK Hls H LFILL; lia)).
assert (SEG' : seg_loop (zdrop segptr (lacing_of hdr)) (negb (bosv =? 0)) (os_lacing_fill os3) (os_lacing_packet os3) (-1) = (lac, gran, f', p', sv')).
{ unfold lacing_of. rewrite zdrop_zslice by lia. rewrite <- Enb. replace (27 + segptr) with (27 + segptr) by lia. exact SEG. }
pose proof (rw_cells_bound _ _ _ _ OS2) as GB2.
unfold stream_cells, X1ix.os_fp, set_lacing, wz in OS2. cbn [os_body_storage os_body_fill os_body_returned os_lacing_storage os_lacing_fill os_lacing_packet os_lacing_returned
os_header_fill os_e_o_s os_b_o_s os_serialno os_pageno os_packetno os_granulepos] in OS2.
clear MU WM. pose proof (munch_refl W m2) as MUb. pose proof (wmono_refl rsegs m2) as WMb.

zstep. rewrite (swrap32_sextw sv') by (clear - SL5 SL3 gws2 lws2 sv' p' f' Enb nb Hbv LL F6 F5 F4 gws lws SEP_HG SEP_HL SEP_LG LPK LFILL Hseg Hls HL LENH bosv segptr os3 hs shdr H Gv L Bd; lia).
zstep. zstep. if_cases CSV; zify_cond CSV.
all: rewrite land_ones64 in CSV.
+
assert (Esv : sv' = -1) by (destruct (Z.eq_dec sv' (-1)) as [E|NE]; [exact E| rewrite Z.mod_small in CSV by (clear - NE CSV SL5 SL4 SL3 gws2 lws2 sv' p' f' Enb nb CL Hbv LL HB0 F6 F4 gws lws SEP_HG SEP_HL SEP_LG TOPH TOPL HGv LPK LFILL Hls HL LENH bosv segptr os3 hs shdr H Gv L Bd; lia); (clear - NE CSV SL5 SL3 gws2 lws2 sv' p' f' Enb nb Hbv LL HB0 gws lws SEP_HG SEP_HL SEP_LG TOPH TOPG TOPL HGv HLv Hls HL LENH bosv segptr os3 hs shdr H Gv L Bd; lia)]).
subst sv'.
eapply (pi_tail m m2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lac gran f' p' (-1) lws2 gws2 SEG');
cbv zeta; try eassumption; try (clear - SL4 p' f' F6 os3 SL3 gws2 lws2 Enb nb CL Hbv LL gws lws SEP_HG SEP_HL SEP_LG LFILL Hls HL LENH bosv segptr hs shdr H Gv L Bd; lia).
all: first [ unfold zlength in *; rewrite ?app_length, ?Nat2Z.inj_add; (clear - SL3 SL1 gws2 lws2 p' f' gran lac Enb nb CL Hbv LL gws lws SEP_HG SEP_HL SEP_LG LFILL Hseg Hls HL LENH bosv segptr os3 hs shdr H Gv L Bd; lia)
| apply Forall_app; split; [exact LOK| eapply Forall_impl; [| exact SLV]; cbv beta; intros; (clear - H0 a; lia)]
| exact OS2 ].
+
assert (Hsv : 0 <= sv' < f') by (destruct (Z.eq_dec sv' (-1)) as [E|NE]; [exfalso; rewrite E in CSV; apply CSV; reflexivity| lia]).
zstep. zstep. zstep. rewrite !Z.shiftl_mul_pow2 by lia. change (2^3) with 8.
cbn [app] in FR2. zstep.
pose proof (u64arr_store_ok rsegs _ _ _ sv' (wa (Gv + sv' * 8)) GRA2 ltac:(unfold zlength in *; rewrite ?app_length in *; lia) ltac:(f_equal; lia)) as SOK.
zstep.
replace (Z_to_bv 64 (Gv + sv' * 8)) with (wa (Gv + 8 * sv')) by (unfold wa; f_equal; lia).
unfold wz.
pose proof (u64arr_write rsegs _ _ _ sv' (Z_to_bv 64 (ogg_page_granulepos hdr)) GRA2 ltac:(unfold zlength in *; rewrite ?app_length in *; lia)) as GRA3. clear GRA2.
store_done. rename GRA3 into GRA2.
eapply (pi_tail m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lac gran f' p' sv' lws2 (upd gws2 (Z.to_nat sv') (Z_to_bv 64 (ogg_page_granulepos hdr))) SEG');
cbv zeta; try eassumption; try (clear - SL4 p' f' F6 os3 Hsv SL3 gws2 lws2 sv' Enb nb Hbv LL gws lws SEP_HG SEP_HL SEP_LG Hls HL LENH bosv segptr hs shdr H Gv L Bd; lia).
all: first [ rewrite upd_length; exact GL2
| unfold zlength in *; rewrite ?app_length, ?Nat2Z.inj_add; (clear - Hsv SL3 SL1 gws2 lws2 sv' p' f' gran lac Enb nb CL Hbv LL gws lws SEP_HG SEP_HL SEP_LG LFILL Hseg Hls HL LENH bosv segptr os3 hs shdr H Gv L Bd; lia)
| apply Forall_app; split; [exact LOK| eapply Forall_impl; [| exact SLV]; cbv beta; intros; (clear - H0 a; lia)]
| eapply munch_trans; [exact MU2| exact MUb]
| eapply wmono_trans; [exact WM2| exact WMb]
| lazymatch goal with |- rw_cells _ _ _ (stream_cells _ _ _ _ _) => lazymatch goal with OSx : rw_cells rsegs _ A _ |- _ => exact OSx end end
| lazymatch goal with |- rw_cells _ _ _ (_ ++ _) => lazymatch goal with FRx : rw_cells rsegs _ (bv_unsigned sp + -144) _ |- _ => exact FRx end end ].
Qed.
End PIF.
