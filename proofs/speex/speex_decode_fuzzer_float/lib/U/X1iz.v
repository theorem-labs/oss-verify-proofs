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

Lemma u32_low_byte : forall m L l ws (i : Z) a,
u32arr rsegs m L ws -> wpre l ws -> 0 <= i -> (Z.to_nat i < length l)%nat -> 0 <= znth l i < 2^32 -> a = wa (L + 4 * i) ->
ov_read_bytes rsegs m a 1 = Some [Z_to_bv 8 (znth l i)].
Proof.
intros m L l ws i a [HB HW] PRE Hi Hl Hv ->.
pose proof (wpre_nth l ws i PRE Hi Hl) as E.
assert (HL : (Z.to_nat i < length ws)%nat) by (destruct PRE; lia).
pose proof (nth_error_nth' ws (Z_to_bv 64 0) HL) as X. rewrite E in X.
first [ pose proof (u32s_split ws (Z.to_nat i) _ X) as sfP_; sf_destruct 6%nat sfP_ as pre post Ews Hlen Eu Hlu | sf_fb; destruct (u32s_split ws (Z.to_nat i) _ X) as (pre & post & Ews & Hlen & Eu & Hlu) ].
replace (L + 4 * i) with (L + Z.of_nat (4 * Z.to_nat i)) by lia.
rewrite (bytes_at_ov_read rsegs m L (u32s ws) (4 * Z.to_nat i) 1 HB) by (rewrite Eu, !app_length, length_le4, Hlu; lia).
rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag, skipn_O by lia.
unfold le4, wz. rewrite Z_to_bv_unsigned. cbn [Z_to_le_bytes app firstn]. f_equal. f_equal.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2^8). change (bv_modulus 64) with (2^64).
rewrite (Z.mod_small (znth l i) (2^64)) by lia. reflexivity.
Qed.

Lemma zslice_snoc : forall off k (l : list Z), 0 <= off -> (Z.to_nat off + S k <= length l)%nat ->
zslice off (Z.of_nat (S k)) l = zslice off (Z.of_nat k) l ++ [znth l (off + Z.of_nat k)].
Proof.
intros off k l Ho Hl. revert off Ho Hl. induction k as [|k IH]; intros off Ho Hl.
- rewrite zslice_S by (unfold zlength; lia). rewrite !zslice_0. cbn. f_equal. f_equal. lia.
- rewrite zslice_S by (unfold zlength; lia). rewrite (zslice_S off k) by (unfold zlength; lia).
rewrite IH by lia. cbn [app]. f_equal. f_equal. f_equal. f_equal. lia.
Qed.

Lemma firstn_add_skipn : forall {X} (l : list X) a b, firstn (a + b) l = firstn a l ++ firstn b (skipn a l).
Proof.
induction l as [|x l IH]; intros [|a] b; cbn; try reflexivity; [rewrite firstn_nil; reflexivity|]. f_equal. apply IH.
Qed.
Lemma zslice_app : forall off a b (l : list Z), 0 <= off -> 0 <= a -> 0 <= b ->
zslice off (a + b) l = zslice off a l ++ zslice (off + a) b l.
Proof.
intros off a b l Ho Ha Hb. unfold zslice, ztake, zdrop.
destruct (Z.ltb_spec off 0); [lia|]. destruct (Z.ltb_spec (off + a) 0); [lia|].
replace (Z.to_nat (a + b)) with (Z.to_nat a + Z.to_nat b)%nat by lia.
rewrite firstn_add_skipn, skipn_skipn. f_equal. f_equal. f_equal. lia.
Qed.

Section PIS.
Context {RCEIL : RunCeiling}.
Variables (A Bd L Gv H Bp blen : Z) (shdr hs : list byte) (os2 : stream_st bptr) (lws : list word) (m : mem).
Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
Variables (x1 : word) (pn : Z) (x5 x6 x7 x14 x15 x16 x17 x18 x22 x27 x28 x29 x30 x31 : word).
Local Notation hdr := (ubytes hs).
Local Notation nseg := (znth (ubytes hs) 26).
Local Notation fl := (znth (ubytes hs) 5).
Hypothesis LENH : length hs = (27 + Z.to_nat nseg)%nat.
Hypothesis Hnseg : 0 <= nseg < 256.
Hypothesis HL : length shdr = 284%nat.
Hypothesis FOK : stream_fields_ok os2.
Hypothesis LFILL : zlength (os_lacing os2) = os_lacing_fill os2.
Hypothesis LOK : lacing_vals_ok (os_lacing os2).
Hypothesis LPRE : wpre (os_lacing os2) lws.
Hypothesis HH : 0 <= H. Hypothesis TOPH : H + Z.of_nat (length hs) < 2^63.
Hypothesis HBp : 0 <= Bp. Hypothesis Hblen : zsum (lacing_of hdr) <= blen. Hypothesis TOPB : Bp + blen < 2^63.
Hypothesis TOPL : L + 4 * Z.of_nat (length lws) < 2^63.
Hypothesis OS : rw_cells rsegs m A (stream_cells Bd L Gv shdr os2).
Hypothesis LAC : u32arr rsegs m L lws.
Hypothesis HS : bytes_at rsegs m H hs.
Hypothesis MI : mem_inv rsegs m.

Local Notation ST pc x10 x11 x12 x13 x19 x20 x23 x25 :=
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp x5 x6 x7 (Z_to_bv 64 A) (Z_to_bv 64 fl) x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 (Z_to_bv 64 H) x22 x23 (Z_to_bv 64 pn) x25 (Z_to_bv 64 nseg) x27 x28 x29 x30 x31)
F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

Definition skip_exit (bos' segptr skipped : Z) : machine_state -> Prop :=
fun ms' => exists (x10 x11 x12 x13 : word),
ms' = ST (if blen - skipped =? 0 then 0x30afc else 0x30ac8) x10 x11 x12 x13
(Z_to_bv 64 (blen - skipped)) (Z_to_bv 64 (Bp + skipped)) (Z_to_bv 64 segptr) (Z_to_bv 64 bos')
/\ 0 <= skipped <= zsum (lacing_of hdr) /\ 0 <= segptr <= nseg /\ (bos' = 0 \/ bos' = Z.land fl 2).

Ltac name_hbyte k b Hb R HS :=
pose proof (bytes_at_read1 rsegs _ H hs k _ HS ltac:(lia) ltac:(lia) eq_refl) as R;
pose proof (byte_range (nth (Z.to_nat k) hs (Z_to_bv 8 0))) as Hb;
set (b := bv_unsigned (nth (Z.to_nat k) hs (Z_to_bv 8 0))) in Hb.

#[using="shdr lws LENH Hnseg HL HBp Hblen TOPB HS"] Lemma pi_loop2 : forall (k : nat) (i acc : Z) (x13 : word),
Z.to_nat (nseg - i) = k -> 0 <= i < nseg -> acc = zsum (zslice 27 i hdr) -> acc = 255 * i ->
evt rsegs (fun ms' => let '(n, s) := skip_continued (zslice (27 + i) (nseg - i) hdr) in skip_exit 0 (i + n) (acc + s) ms')
(ST 0x30a8c (Z_to_bv 64 (H + 27 + i)) (Z_to_bv 64 255) (Z_to_bv 64 (nseg - i)) x13
(Z_to_bv 64 (blen - acc)) (Z_to_bv 64 (Bp + acc)) (Z_to_bv 64 (i + 1)) (Z_to_bv 64 (Z.land fl 2))).
Proof.
induction k as [|k IH]; intros i acc x13 Hk Hi Hacc Hacc2; [lia|].
pose proof HS as (HB0 & HB1 & HB).
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof (byte_range (nth (Z.to_nat 5) hs (Z_to_bv 8 0))) as Hfl. rewrite <- (znth_ubytes hs 5) in Hfl by lia.
pose proof (Z_land_range fl 2 ltac:(lia) ltac:(lia)) as Hb2.
assert (ZS : zsum (zslice 27 i hdr) + zsum (zslice (27 + i) (nseg - i) hdr) = zsum (lacing_of hdr)).
{ unfold lacing_of. rewrite <- zsum_app, <- zslice_app by lia. f_equal. f_equal. lia. }
pose proof (zsum_nonneg (zslice (27 + i + 1) (nseg - i - 1) hdr) ltac:(eapply Forall_impl; [| apply bytes_ok_zslice; apply ubytes_ok]; cbv beta; intros; lia)) as ZN.
name_hbyte (27 + i) v Hv Rv HS.
assert (ZR : zsum (zslice (27 + i) (nseg - i) hdr) = v + zsum (zslice (27 + i + 1) (nseg - i - 1) hdr)).
{ rewrite (zslice_cons (27 + i)) by (rewrite ?zlength_ubytes; unfold zlength; lia).
replace (znth hdr (27 + i)) with v by (unfold v; symmetry; apply znth_ubytes; lia). reflexivity. }

zstep. zstep. zstep.
zstep. if_cases CV; zify_cond CV; rewrite ?unsigned_lit in CV by lia.
all: fold v; replace (blen - acc + - v) with (blen - (acc + v)) by lia; replace (Bp + acc + v) with (Bp + (acc + v)) by lia.
-
fold v in CV.
rewrite (zslice_cons (27 + i)) by (rewrite ?zlength_ubytes; unfold zlength; lia). cbn [skip_continued].
replace (znth hdr (27 + i)) with v by (unfold v; symmetry; apply znth_ubytes; lia).
replace (v <? 255) with true by (symmetry; apply Z.ltb_lt; lia).
assert (Hv2 : v <= zsum (zslice (27 + i) (nseg - i) hdr)).
{ rewrite (zslice_cons (27 + i)) by (rewrite ?zlength_ubytes; unfold zlength; lia).
replace (znth hdr (27 + i)) with v by (unfold v; symmetry; apply znth_ubytes; lia). cbn [zsum].
replace (27 + i + 1) with (27 + i + 1) by lia. replace (nseg - i - 1) with (nseg - i - 1) by lia. lia. }
zstep. zstep. if_cases CBZ; zify_cond CBZ; rewrite ?unsigned_lit, ?land_ones64, ?Z.mod_small in CBZ by lia.
+ apply evt_done. unfold skip_exit. replace (blen - (acc + v) =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
sf_eexists 4%nat. split; [reflexivity|]. unfold lacing_of in *. lia.
+ zstep. apply evt_done. unfold skip_exit. replace (blen - (acc + v) =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
sf_eexists 4%nat. split; [reflexivity|]. unfold lacing_of in *. lia.
-
fold v in CV.
rewrite (zslice_cons (27 + i)) by (rewrite ?zlength_ubytes; unfold zlength; lia). cbn [skip_continued].
replace (znth hdr (27 + i)) with v by (unfold v; symmetry; apply znth_ubytes; lia).
replace (v <? 255) with false by (symmetry; apply Z.ltb_ge; lia).
assert (Hacc3 : acc + 255 = zsum (zslice 27 (i + 1) hdr)).
{ rewrite zslice_app, zsum_app, <- Hacc by lia. rewrite (zslice_cons (27 + i)), zslice_0 by (rewrite ?zlength_ubytes; unfold zlength; lia).
replace (znth hdr (27 + i)) with v by (unfold v; symmetry; apply znth_ubytes; lia). cbn. lia. }
zstep. rewrite (swrap32_small (i + 1 + 1)) by lia.
zstep. zstep.
zstep. if_cases CE; zify_cond CE; rewrite ?unsigned_lit, ?land_ones64, ?Z.mod_small in CE by lia.
+
eapply evt_mono.
{ replace (H + 27 + i + 1) with (H + 27 + (i + 1)) by lia. replace (nseg - i + -1) with (nseg - (i + 1)) by lia.
replace (blen - (acc + v)) with (blen - (acc + 255)) by lia. replace (Bp + (acc + v)) with (Bp + (acc + 255)) by lia.
replace (i + 2) with (i + 1 + 1) by lia.
eapply (IH (i + 1) (acc + 255)); lia. }
cbv beta. intros ms' PO. replace (27 + i + 1) with (27 + (i + 1)) by lia. replace (nseg - i - 1) with (nseg - (i + 1)) by lia.
destruct (skip_continued (zslice (27 + (i + 1)) (nseg - (i + 1)) hdr)) as [n s].
replace (i + (n + 1)) with (i + 1 + n) by lia. replace (acc + (s + v)) with (acc + 255 + s) by lia. exact PO.
+
replace (nseg - i - 1) with 0 by lia. rewrite zslice_0. cbn [skip_continued].
zstep. zstep. zstep. if_cases CBZ; zify_cond CBZ; rewrite ?unsigned_lit, ?land_ones64, ?Z.mod_small in CBZ by lia.
* apply evt_done. unfold skip_exit. replace (blen - (acc + (0 + v)) =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
replace (blen - (acc + v)) with (blen - (acc + (0 + v))) by lia. replace (Bp + (acc + v)) with (Bp + (acc + (0 + v))) by lia.
replace (i + (0 + 1)) with nseg by lia.
sf_eexists 4%nat. split; [reflexivity|]. unfold lacing_of in *. lia.
* zstep. apply evt_done. unfold skip_exit. replace (blen - (acc + (0 + v)) =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
replace (blen - (acc + v)) with (blen - (acc + (0 + v))) by lia. replace (Bp + (acc + v)) with (Bp + (acc + (0 + v))) by lia.
replace (i + (0 + 1)) with nseg by lia.
sf_eexists 4%nat. split; [reflexivity|]. unfold lacing_of in *. lia.
Qed.

#[using="Type"] Lemma low8_land : forall v, low8 v = Z.land v 255.
Proof. intros. reflexivity. Qed.

#[using="shdr lws LENH Hnseg HL HBp Hblen TOPB HS"] Lemma pi_doskip : forall (x10 x11 x12 x13 x23 : word),
evt rsegs (fun ms' => let '(n, s) := skip_continued (lacing_of hdr) in skip_exit 0 n s ms')
(ST 0x30a78 x10 x11 x12 x13 (Z_to_bv 64 blen) (Z_to_bv 64 Bp) x23 (Z_to_bv 64 (Z.land fl 2))).
Proof.
intros.
pose proof HS as (HB0 & HB1 & HB).
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof (byte_range (nth (Z.to_nat 5) hs (Z_to_bv 8 0))) as Hfl. rewrite <- (znth_ubytes hs 5) in Hfl by lia.
pose proof (Z_land_range fl 2 ltac:(lia) ltac:(lia)) as Hb2.
pose proof (zsum_nonneg (lacing_of hdr) ltac:(eapply Forall_impl; [| apply bytes_ok_zslice; apply ubytes_ok]; cbv beta; intros; lia)) as ZN0.

zstep. if_cases CN; zify_cond CN; rewrite ?unsigned_lit in CN by lia.
-
unfold lacing_of. replace (zslice 27 nseg hdr) with (@nil Z) by (rewrite CN, zslice_0; reflexivity). cbn [skip_continued].
zstep. zstep. zstep. if_cases CBZ; zify_cond CBZ; rewrite ?unsigned_lit, ?land_ones64, ?Z.mod_small in CBZ by lia.
+ apply evt_done. unfold skip_exit. rewrite Z.sub_0_r, Z.add_0_r. replace (blen =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
sf_eexists 4%nat. split; [reflexivity|]. lia.
+ apply evt_done. unfold skip_exit. rewrite Z.sub_0_r, Z.add_0_r. replace (blen =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
sf_eexists 4%nat. split; [reflexivity|]. lia.
-
zstep. zstep. zstep. zstep.
eapply evt_mono.
{ replace (H + 27) with (H + 27 + 0) by lia. replace blen with (blen - 0) at 1 by lia. replace Bp with (Bp + 0) at 1 by lia.
replace (Z_to_bv 64 nseg) with (Z_to_bv 64 (nseg - 0)) at 1 by (f_equal; lia).
eapply (pi_loop2 (Z.to_nat nseg) 0 0); try lia. rewrite zslice_0. reflexivity. }
cbv beta. intros ms' PO. unfold lacing_of. rewrite Z.add_0_r, Z.sub_0_r in PO.
destruct (skip_continued (zslice 27 nseg hdr)) as [n s]. rewrite !Z.add_0_l in PO. exact PO.
Qed.

#[using="Bd L Gv shdr lws LENH Hnseg HL FOK LFILL LOK LPRE HBp Hblen TOPB OS LAC HS"] Lemma pi_skip : forall (x11 x12 x13 x23 x25 : word),
evt rsegs (fun ms' => let '(bos', segptr, skipped) := pagein_skip os2 hdr in skip_exit bos' segptr skipped ms')
(ST 0x30a50 (Z_to_bv 64 (Z.land fl 1)) x11 x12 x13 (Z_to_bv 64 blen) (Z_to_bv 64 Bp) x23 x25).
Proof.
intros.
pose proof FOK as sfP_; first [ sf_destruct 12%nat sfP_ as F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 | sf_fb; destruct sfP_ as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12) ]. unfold int31 in *.
pose proof HS as (HB0 & HB1 & HB). pose proof (wpre_length _ _ LPRE) as LL. unfold zlength in LFILL.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof (byte_range (nth (Z.to_nat 5) hs (Z_to_bv 8 0))) as Hfl. rewrite <- (znth_ubytes hs 5) in Hfl by lia.
pose proof (Z_land_range fl 2 ltac:(lia) ltac:(lia)) as Hb2. pose proof (Z_land_range fl 1 ltac:(lia) ltac:(lia)) as Hb1.
pose proof (rw_cells_bound _ _ _ _ OS) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof (zsum_nonneg (lacing_of hdr) ltac:(eapply Forall_impl; [| apply bytes_ok_zslice; apply ubytes_ok]; cbv beta; intros; lia)) as ZN0.
unfold stream_cells, wz in OS.
unfold pagein_skip, ogg_page_continued, ogg_page_bos.

zstep. zstep. if_cases CC; zify_cond CC; rewrite ?unsigned_lit in CC by lia.
-
replace (Z.land fl 1 =? 0) with true by (symmetry; apply Z.eqb_eq; exact CC). cbn [negb].
zstep. zstep. if_cases CBZ; zify_cond CBZ; rewrite ?unsigned_lit, ?land_ones64, ?Z.mod_small in CBZ by lia.
+ apply evt_done. unfold skip_exit. rewrite Z.sub_0_r, Z.add_0_r. replace (blen =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
sf_eexists 4%nat. split; [reflexivity|]. lia.
+ apply evt_done. unfold skip_exit. rewrite Z.sub_0_r, Z.add_0_r. replace (blen =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
sf_eexists 4%nat. split; [reflexivity|]. lia.
- replace (Z.land fl 1 =? 0) with false by (symmetry; apply Z.eqb_neq; exact CC). cbn [negb].

zstep. zstep. if_cases CF; zify_cond CF.
+
assert (Hf0 : os_lacing_fill os2 <= 0) by (destruct (Z.ltb_spec 0 (os_lacing_fill os2)); destruct (Z.ltb_spec (os_lacing_fill os2) 9223372036854775808); cbn in CF; try discriminate; lia).
replace (os_lacing_fill os2 <? 1) with true by (symmetry; apply Z.ltb_lt; lia). cbn [orb].
eapply evt_mono; [eapply pi_doskip|]. cbv beta. intros ms' PO. destruct (skip_continued (lacing_of hdr)) as [n s]. exact PO.
+
replace (os_lacing_fill os2 <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [orb].
pose proof (Forall_znth _ _ (os_lacing_fill os2 - 1) LOK ltac:(cbv beta; lia)) as Rl. cbv beta in Rl.
zstep. zstep. zstep. rewrite !Z.shiftl_mul_pow2 by lia. change (2^2) with 4.
pose proof (u32_low_byte m L (os_lacing os2) lws (os_lacing_fill os2 - 1) (wa (L + os_lacing_fill os2 * 4 + -4)) LAC LPRE
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(f_equal; lia)) as RB.
zstep. zstep.
zstep. if_cases CL; zify_cond CL; rewrite ?unsigned_lit in CL by lia.
all: rewrite Z_to_bv_unsigned in CL; unfold bv_wrap in CL; change (bv_modulus 8) with (2^8) in CL.
all: pose proof (Z.land_ones (znth (os_lacing os2) (os_lacing_fill os2 - 1)) 8 ltac:(lia)) as L8; change (Z.ones 8) with 255 in L8.
all: pose proof (Z.mod_pos_bound (znth (os_lacing os2) (os_lacing_fill os2 - 1)) (2^8) ltac:(lia)) as M8.
*
replace (Z.land (znth (os_lacing os2) (os_lacing_fill os2 - 1)) 255 <? 255) with false by (symmetry; apply Z.ltb_ge; lia).
replace (znth (os_lacing os2) (os_lacing_fill os2 - 1) =? 1024) with false.
2:{ symmetry. apply Z.eqb_neq. intros E. rewrite E in L8. change (1024 mod 2^8) with 0 in L8. rewrite E in CL. change (1024 mod 2^8) with 0 in CL. lia. }
cbn [orb].
zstep. zstep. if_cases CBZ; zify_cond CBZ; rewrite ?unsigned_lit, ?land_ones64, ?Z.mod_small in CBZ by lia.
-- apply evt_done. unfold skip_exit. rewrite Z.sub_0_r, Z.add_0_r. replace (blen =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
sf_eexists 4%nat. split; [reflexivity|]. lia.
-- apply evt_done. unfold skip_exit. rewrite Z.sub_0_r, Z.add_0_r. replace (blen =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
sf_eexists 4%nat. split; [reflexivity|]. lia.
* replace (Z.land (znth (os_lacing os2) (os_lacing_fill os2 - 1)) 255 <? 255) with true by (symmetry; apply Z.ltb_lt; lia). cbn [orb].
eapply evt_mono; [eapply pi_doskip|]. cbv beta. intros ms' PO. destruct (skip_continued (lacing_of hdr)) as [n s]. exact PO.
Qed.
End PIS.
