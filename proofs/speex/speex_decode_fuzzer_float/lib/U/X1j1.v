(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1cc X1bk X1bj X1cf X1bu.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1fe X1ik X1ii X1iu X1it X1iq X1in X1ix.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qz X1r0 X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma u32s_firstn : forall n ws, firstn (4 * n) (u32s ws) = u32s (firstn n ws).
Proof.
induction n as [|n IH]; intros ws; [cbn; reflexivity|].
destruct ws as [|w ws]; [cbn; destruct (4 * S n)%nat; reflexivity|]. cbn [u32s firstn].
rewrite firstn_app, length_le4, firstn_all2 by (rewrite length_le4; lia).
replace (4 * S n - 4)%nat with (4 * n)%nat by lia. rewrite IH. reflexivity.
Qed.
Lemma u32s_skipn : forall n ws, skipn (4 * n) (u32s ws) = u32s (skipn n ws).
Proof.
induction n as [|n IH]; intros ws; [cbn; reflexivity|].
destruct ws as [|w ws]; [cbn; destruct (4 * S n)%nat; reflexivity|]. cbn [u32s skipn].
rewrite skipn_app, length_le4, skipn_all2 by (rewrite length_le4; lia).
replace (4 * S n - 4)%nat with (4 * n)%nat by lia. rewrite IH. reflexivity.
Qed.
Lemma u64s_firstn : forall n ws, firstn (8 * n) (u64s ws) = u64s (firstn n ws).
Proof.
induction n as [|n IH]; intros ws; [cbn; reflexivity|].
destruct ws as [|w ws]; [cbn; destruct (8 * S n)%nat; reflexivity|]. cbn [u64s firstn].
rewrite firstn_app, length_le8, firstn_all2 by (rewrite length_le8; lia).
replace (8 * S n - 8)%nat with (8 * n)%nat by lia. rewrite IH. reflexivity.
Qed.
Lemma u64s_skipn : forall n ws, skipn (8 * n) (u64s ws) = u64s (skipn n ws).
Proof.
induction n as [|n IH]; intros ws; [cbn; reflexivity|].
destruct ws as [|w ws]; [cbn; destruct (8 * S n)%nat; reflexivity|]. cbn [u64s skipn].
rewrite skipn_app, length_le8, skipn_all2 by (rewrite length_le8; lia).
replace (8 * S n - 8)%nat with (8 * n)%nat by lia. rewrite IH. reflexivity.
Qed.

Lemma u32_move : forall ws k n, (k + n <= length ws)%nat ->
firstn (4 * n) (skipn (4 * k) (u32s ws)) ++ skipn (4 * n) (u32s ws) = u32s (firstn n (skipn k ws) ++ skipn n ws).
Proof. intros. rewrite u32s_skipn, u32s_firstn, u32s_skipn, u32s_app. reflexivity. Qed.
Lemma u64_move : forall ws k n, (k + n <= length ws)%nat ->
firstn (8 * n) (skipn (8 * k) (u64s ws)) ++ skipn (8 * n) (u64s ws) = u64s (firstn n (skipn k ws) ++ skipn n ws).
Proof. intros. rewrite u64s_skipn, u64s_firstn, u64s_skipn, u64s_app. reflexivity. Qed.

Lemma u32arr_u8 : forall m A ws, u32arr rsegs m A ws -> u8arr rsegs m A (u32s ws).
Proof. intros m A ws [HB HW]. split; [exact HB|]. rewrite u32s_length, Nat2Z.inj_mul. exact HW. Qed.
Lemma u8_u32arr : forall m A ws, u8arr rsegs m A (u32s ws) -> u32arr rsegs m A ws.
Proof. intros m A ws [HB HW]. split; [exact HB|]. rewrite u32s_length, Nat2Z.inj_mul in HW. exact HW. Qed.
Lemma u64arr_u8 : forall m A ws, u64arr rsegs m A ws -> u8arr rsegs m A (u64s ws).
Proof. intros m A ws [HB HW]. split; [exact HB|]. rewrite u64s_length, Nat2Z.inj_mul. exact HW. Qed.
Lemma u8_u64arr : forall m A ws, u8arr rsegs m A (u64s ws) -> u64arr rsegs m A ws.
Proof. intros m A ws [HB HW]. split; [exact HB|]. rewrite u64s_length, Nat2Z.inj_mul in HW. exact HW. Qed.

Lemma wpre_move : forall l ws k, wpre l ws -> (k <= length l)%nat ->
wpre (skipn k l) (firstn (length l - k) (skipn k ws) ++ skipn (length l - k) ws).
Proof.
intros l ws k [P L] Hk. unfold wpre. rewrite skipn_length, app_length, firstn_length_le, skipn_length by (rewrite skipn_length; lia).
split; [|lia]. rewrite firstn_app, firstn_firstn, Nat.min_id, firstn_length_le, Nat.sub_diag, firstn_O, app_nil_r by (rewrite skipn_length; lia).
rewrite <- skipn_map, <- P, skipn_firstn_comm. reflexivity.
Qed.

Definition ret_body (os : stream_st bptr) : stream_st bptr :=
if negb (os_body_returned os =? 0) then
set_body os (ztake (os_body_fill os - os_body_returned os) (zdrop (os_body_returned os) (os_body os)))
(os_body_storage os) (os_body_fill os - os_body_returned os) 0
else os.
Definition ret_lacing (os : stream_st bptr) : stream_st bptr :=
if negb (os_lacing_returned os =? 0) then
set_lacing os (zdrop (os_lacing_returned os) (os_lacing os)) (zdrop (os_lacing_returned os) (os_granules os)) (os_lacing_storage os)
(os_lacing_fill os - os_lacing_returned os) (os_lacing_packet os - os_lacing_returned os) 0
else os.
Lemma pagein_returned_eq : forall os : stream_st bptr, pagein_returned os = ret_lacing (ret_body os).
Proof.
intros os. unfold pagein_returned, ret_lacing, ret_body.
destruct (negb (os_body_returned os =? 0)); reflexivity.
Qed.

Definition hideP (P : Prop) : Prop := P.
Ltac hide H := lazymatch type of H with ?T => change T with (hideP T) in H end.
Ltac unhide := unfold hideP in *.

Lemma serialno_pieces : forall hs : list byte, (18 <= length hs)%nat ->
Z_to_bv 64 (Z.lor
((Z.lor (Z.lor (Z.land (Z.shiftl (bv_unsigned (nth (Z.to_nat 15) hs (Z_to_bv 8 0))) 8) 18446744073709551615)
(bv_unsigned (nth (Z.to_nat 14) hs (Z_to_bv 8 0))))
(Z.land (Z.shiftl (bv_unsigned (nth (Z.to_nat 16) hs (Z_to_bv 8 0))) 16) 18446744073709551615)) mod 2^64)
((bv_swrap 32 (Z.shiftl (bv_unsigned (nth (Z.to_nat 17) hs (Z_to_bv 8 0))) 24)) mod 2^64))
= Z_to_bv 64 (ogg_page_serialno (ubytes hs)).
Proof.
intros hs LEN. unfold ogg_page_serialno, le32_at.
change (zslice 14 4 (ubytes hs)) with (zslice 14 (Z.of_nat 4) (ubytes hs)).
rewrite !zslice_S by (rewrite ?zlength_ubytes; lia). rewrite zslice_0.
norm_lit_idx. rewrite !znth_ubytes by lia. cbn [le_val].
word_bits.
Qed.

Section PIE.
Context {RCEIL : RunCeiling}.
Variables (A G Dsy Bd L Gv lo : Z) (og : page) (shdr hs : list byte) (os : stream_st bptr).
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Local Notation H := (Dsy + pg_hdr og).
Local Notation hdr := (ubytes hs).
Local Notation nseg := (znth (ubytes hs) 26).
Local Notation fl := (znth (ubytes hs) 5).
Local Notation ls := (os_lacing_storage os).
Local Notation bs := (os_body_storage os).
Local Notation W := [(bv_unsigned sp - 144, bv_unsigned sp); (A, A + 408); (Bd, Bd + bs); (L, L + 4 * ls); (Gv, Gv + 8 * ls)].
Hypothesis LENH : length hs = (27 + Z.to_nat nseg)%nat.
Hypothesis HLEN : Z.of_nat (length hs) = pg_header_len og.
Hypothesis Hnseg : 0 <= nseg < 256.
Hypothesis HL : length shdr = 284%nat.
Hypothesis FOK : stream_fields_ok os.
Hypothesis INV : 0 <= os_lacing_returned os <= os_lacing_packet os /\ os_lacing_packet os <= os_lacing_fill os /\ os_lacing_fill os <= ls.
Hypothesis BINV : 0 <= os_body_returned os <= os_body_fill os /\ os_body_fill os <= bs /\ bs < 2^62.
Hypothesis LFILL : zlength (os_lacing os) = os_lacing_fill os.
Hypothesis BFILL : zlength (os_body os) = os_body_fill os.
Hypothesis LOK : lacing_vals_ok (os_lacing os).
Hypothesis HA : 0 < A. Hypothesis HG : 0 < G. Hypothesis HBd : 0 < Bd. Hypothesis HLv : 0 < L. Hypothesis HGv : 0 < Gv. Hypothesis HDsy : 0 <= Dsy.
Hypothesis Hpg : 0 <= pg_hdr og. Hypothesis Hbl : 0 <= pg_body_len og.
Hypothesis TOPB : Bd + bs < 2^63. Hypothesis TOPL : L + 4 * ls < 2^63. Hypothesis TOPG : Gv + 8 * ls < 2^63.
Hypothesis TOPH : H + Z.of_nat (length hs) + pg_body_len og < 2^63.
Hypothesis LOSP : lo + 144 <= bv_unsigned sp.
Hypothesis SPA : bv_unsigned sp <= A. Hypothesis SPG : bv_unsigned sp <= G.
Hypothesis SEP_AG : A + 408 <= G \/ G + 32 <= A.
Hypothesis SEP_fB : Bd + bs <= lo. Hypothesis SEP_fL : L + 4 * ls <= lo. Hypothesis SEP_fG : Gv + 8 * ls <= lo.
Hypothesis SEP_Hf : H + Z.of_nat (length hs) <= lo.
Hypothesis SEP_BL : Bd + bs <= L \/ L + 4 * ls <= Bd.
Hypothesis SEP_BG : Bd + bs <= Gv \/ Gv + 8 * ls <= Bd.
Hypothesis SEP_LG : L + 4 * ls <= Gv \/ Gv + 8 * ls <= L.
Hypothesis SEP_HB : H + Z.of_nat (length hs) <= Bd \/ Bd + bs <= H.
Hypothesis SEP_HL : H + Z.of_nat (length hs) <= L \/ L + 4 * ls <= H.
Hypothesis SEP_HG : H + Z.of_nat (length hs) <= Gv \/ Gv + 8 * ls <= H.
#[local] Set Default Proof Using "LENH HLEN Hnseg HL FOK INV BINV LFILL BFILL LOK HA HG HBd HLv HGv HDsy Hpg Hbl TOPB TOPL TOPG TOPH LOSP SPA SPG SEP_AG SEP_fB SEP_fL SEP_fG SEP_Hf SEP_BL SEP_BG SEP_LG SEP_HB SEP_HL SEP_HG".

Local Notation FRAME m loc := (rw_cells rsegs m (bv_unsigned sp + -144)
(loc ++ [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
Local Notation LOC j0 := [CB 8 j0; C8 (wz (ogg_page_granulepos hdr)); C8 (Z_to_bv 64 (znth hdr 18)); C8 (Z_to_bv 64 (znth hdr 21)); C8 (Z_to_bv 64 fl)].

Definition body_pre (body : list Z) (bytes : list byte) : Prop :=
firstn (length body) (ubytes bytes) = body /\ (length body <= length bytes)%nat.

Definition prologue_post (m : mem) : machine_state -> Prop :=
fun ms' => exists (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word) m' (j0 : list byte) bodybytes' lws' gws',
ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp x5 x6 x7 (Z_to_bv 64 A) x9 x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (-1)) (Z_to_bv 64 (pg_body_len og)) (Z_to_bv 64 (H + pg_header_len og)) (Z_to_bv 64 H) x22
(Z_to_bv 64 (znth hdr 19)) (Z_to_bv 64 (znth hdr 4)) (Z_to_bv 64 (ogg_page_serialno hdr)) (Z_to_bv 64 nseg) (Z_to_bv 64 (znth hdr 20)) x28 x29 x30 x31)
F (Z_to_bv 64 0x309a0) fc None m' (seg_rom rsegs)
/\ munch W m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' A (stream_cells Bd L Gv shdr (pagein_returned os))
/\ u8arr rsegs m' Bd bodybytes' /\ Z.of_nat (length bodybytes') = bs /\ body_pre (os_body (pagein_returned os)) bodybytes'
/\ u32arr rsegs m' L lws' /\ wpre (os_lacing (pagein_returned os)) lws' /\ Z.of_nat (length lws') = ls
/\ u64arr rsegs m' Gv gws' /\ Z.of_nat (length gws') = ls
/\ FRAME m' (LOC j0) /\ bytes_at rsegs m' H hs /\ rw_cells rsegs m' G (page_cells Dsy og) /\ stk rsegs m' lo (bv_unsigned sp + -144).

Lemma pi_lclean : forall m0 m (osb : stream_st bptr) (lws gws : list word) bodybytes' (j0 : list byte)
(x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word),
os_lacing osb = os_lacing os -> os_lacing_storage osb = ls -> os_lacing_fill osb = os_lacing_fill os ->
os_lacing_packet osb = os_lacing_packet os -> os_lacing_returned osb = os_lacing_returned os ->
os_body_storage osb = bs -> 0 <= os_body_fill osb < 2^62 -> 0 <= os_body_returned osb < 2^62 -> stream_fields_ok osb ->
munch W m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
rw_cells rsegs m A (stream_cells Bd L Gv shdr osb) ->
u8arr rsegs m Bd bodybytes' -> Z.of_nat (length bodybytes') = bs -> body_pre (os_body osb) bodybytes' ->
u32arr rsegs m L lws -> wpre (os_lacing os) lws -> Z.of_nat (length lws) = ls ->
u64arr rsegs m Gv gws -> Z.of_nat (length gws) = ls ->
FRAME m (LOC j0) -> bytes_at rsegs m H hs -> rw_cells rsegs m G (page_cells Dsy og) -> stk rsegs m lo (bv_unsigned sp + -144) ->
pagein_returned os = ret_lacing osb ->
evt rsegs (prologue_post m0)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp x5 x6 x7 (Z_to_bv 64 A) (Z_to_bv 64 (os_lacing_returned os)) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (-1)) (Z_to_bv 64 (pg_body_len og)) (Z_to_bv 64 (H + pg_header_len og)) (Z_to_bv 64 H) x22
(Z_to_bv 64 (znth hdr 19)) (Z_to_bv 64 (znth hdr 4)) (Z_to_bv 64 (ogg_page_serialno hdr)) (Z_to_bv 64 nseg) (Z_to_bv 64 (znth hdr 20)) x28 x29 x30 x31)
F (Z_to_bv 64 0x30940) fc None m (seg_rom rsegs)).
Proof.
intros until x31. intros El Els Elf Elp Elr Ebs Hbf Hbr FOKb MU WM MI OS BODY BLEN BPRE LAC LPRE LLEN GRA GLEN FR HS OG ST EPR.

hide SEP_AG. hide SEP_HB. hide SEP_HL. hide SEP_HG. hide SEP_BL. hide SEP_BG. hide BODY. hide HS. hide OG. hide MU. hide WM.
pose proof FOK as sfP_; first [ sf_destruct 12%nat sfP_ as F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 | sf_fb; destruct sfP_ as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12) ].
pose proof FOKb as sfP_; first [ sf_destruct 12%nat sfP_ as Fb1 Fb2 Fb3 Fb4 Fb5 Fb6 Fb7 Fb8 Fb9 Fb10 Fb11 Fb12 | sf_fb; destruct sfP_ as (Fb1 & Fb2 & Fb3 & Fb4 & Fb5 & Fb6 & Fb7 & Fb8 & Fb9 & Fb10 & Fb11 & Fb12) ]. unfold int31 in *.
pose proof INV as (I1 & I2 & I3). unfold zlength in LFILL.
pose proof (rw_cells_bound _ _ _ _ OS) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof (rw_cells_bound _ _ _ _ OG) as GGB. cbn [cells_size csize Nat.add] in GGB.
pose proof HS as (HB0 & HB1 & HB). pose proof (wpre_length _ _ LPRE) as LL.
pose proof (byte_range (nth (Z.to_nat 19) hs (Z_to_bv 8 0))) as H19. rewrite <- (znth_ubytes hs 19) in H19 by lia.
pose proof (byte_range (nth (Z.to_nat 20) hs (Z_to_bv 8 0))) as H20. rewrite <- (znth_ubytes hs 20) in H20 by lia.
pose proof (byte_range (nth (Z.to_nat 4) hs (Z_to_bv 8 0))) as H4. rewrite <- (znth_ubytes hs 4) in H4 by lia.
unfold stream_cells, wz in OS. rewrite Els, Elf, Elp, Elr, Ebs in OS. cbn [app] in FR. unfold page_cells, wz in OG.
pose proof (munch_refl [(bv_unsigned sp + -144, bv_unsigned sp); (A, A + 408); (L, L + 4 * ls); (Gv, Gv + 8 * ls)] m) as MUl. pose proof (wmono_refl rsegs m) as WMl.

zstep. if_cases CLR; zify_cond CLR; rewrite ?unsigned_lit in CLR by lia.
-
apply evt_done. unfold prologue_post. unfold hideP in BODY, HS, OG, MU, WM.
lazymatch type of MUl with munch ?Wl m ?mf =>
pose proof (munch_trans _ _ _ _ MU (munch_weaken Wl W m mf ltac:(unfold sub_fp; cbn [outside]; intros; lia) MUl)) as MU';
pose proof (wmono_trans rsegs _ _ _ WM WMl) as WM';
unfold hideP in SEP_BL, SEP_BG;
pose proof (u8arr_transport rsegs Wl m mf Bd bodybytes' BODY MUl WMl ltac:(cbn [disjoint_from]; lia)) as BODY'; clear SEP_BL SEP_BG;
unfold hideP in SEP_HL, SEP_HG;
pose proof (bytes_at_transport rsegs Wl m mf _ hs HS MUl ltac:(cbn [disjoint_from]; lia)) as HS'; clear SEP_HL SEP_HG;
unfold hideP in SEP_AG;
pose proof (rw_cells_transport rsegs Wl m mf G _ OG MUl WMl ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)) as OG'
end.
sf_eexists 18%nat. lazymatch goal with |- context [MS _ _ _ _ _ ?mx _ = _] => exists mx end. first [ unshelve sf_eexists 4%nat; [ exact (j0) | exact (bodybytes') | exact (lws) | exact (gws) | ] | sf_fb; exists j0, bodybytes', lws, gws ].
split; [reflexivity|]. split; [exact MU'|]. split; [exact WM'|]. split; [assumption|].
rewrite EPR. unfold ret_lacing. rewrite El, Els, Elf, Elp, Elr. replace (os_lacing_returned os =? 0) with true by (symmetry; first [apply Z.eqb_eq; exact CLR | apply Z.eqb_neq; exact CLR]). cbn [negb].
unfold set_lacing, stream_cells, wz. cbn [os_body_data os_body os_body_storage os_body_fill os_body_returned os_lacing_vals os_lacing os_granule_vals os_granules
os_lacing_storage os_lacing_fill os_lacing_packet os_lacing_returned os_header_fill os_e_o_s os_b_o_s os_serialno os_pageno os_packetno os_granulepos].
rewrite ?Els, ?Elf, ?Elp, ?Elr, ?Ebs, ?El.
split; [lazymatch goal with OSx : rw_cells rsegs _ A _ |- _ => exact OSx end|].
split; [exact BODY'|]. split; [exact BLEN|]. split; [exact BPRE|].
split; [exact LAC|]. split; [exact LPRE|]. split; [exact LLEN|].
split; [exact GRA|]. split; [exact GLEN|].
split; [exact FR|]. split; [exact HS'|]. split; [| exact ST]. unfold page_cells, wz. exact OG'.
-
zstep. zstep. zstep. if_cases CE; zify_cond CE; rewrite ?unsigned_lit in CE by lia.
+

zstep. zstep. zstep.
replace (os_lacing_returned os + - os_lacing_returned os) with (os_lacing_fill os - os_lacing_returned os) by lia.
replace (os_lacing_packet os + - os_lacing_returned os) with (os_lacing_packet os - os_lacing_returned os) by lia.
lstep. lstep. lstep.
apply evt_done. unfold prologue_post. unfold hideP in BODY, HS, OG, MU, WM.
lazymatch type of MUl with munch ?Wl m ?mf =>
pose proof (munch_trans _ _ _ _ MU (munch_weaken Wl W m mf ltac:(unfold sub_fp; cbn [outside]; intros; (clear - H x LL bodybytes' gws lws osb sp os shdr Gv L Bd A; lia)) MUl)) as MU';
pose proof (wmono_trans rsegs _ _ _ WM WMl) as WM';
unfold hideP in SEP_BL, SEP_BG;
pose proof (u8arr_transport rsegs Wl m mf Bd bodybytes' BODY MUl WMl ltac:(cbn [disjoint_from]; (clear - LL BLEN bodybytes' gws lws osb SEP_BG SEP_BL SEP_fB SPA LOSP HL LENH sp os hs shdr og lo Gv L Bd Dsy A; lia))) as BODY'; clear SEP_BL SEP_BG;
unfold hideP in SEP_HL, SEP_HG;
pose proof (bytes_at_transport rsegs Wl m mf _ hs HS MUl ltac:(cbn [disjoint_from]; (clear - LL GLEN LLEN bodybytes' gws lws osb SEP_HG SEP_HL SEP_LG SEP_Hf SPA LOSP HL LENH sp os hs shdr og lo Gv L Bd Dsy A; lia))) as HS'; clear SEP_HL SEP_HG;
unfold hideP in SEP_AG;
pose proof (rw_cells_transport rsegs Wl m mf G _ OG MUl WMl ltac:(cbn [disjoint_from cells_size csize Nat.add]; (clear - LL bodybytes' gws lws osb SEP_fG SEP_fL SEP_AG SPG SPA LOSP HL LENH sp os hs shdr og lo Gv L Bd Dsy G A; lia))) as OG'
end.
sf_eexists 18%nat. lazymatch goal with |- context [MS _ _ _ _ _ ?mx _ = _] => exists mx end. first [ unshelve sf_eexists 4%nat; [ exact (j0) | exact (bodybytes') | exact (lws) | exact (gws) | ] | sf_fb; exists j0, bodybytes', lws, gws ].
split; [reflexivity|]. split; [exact MU'|]. split; [exact WM'|]. split; [assumption|].
rewrite EPR. unfold ret_lacing. rewrite El, Els, Elf, Elp, Elr. replace (os_lacing_returned os =? 0) with false by (symmetry; first [apply Z.eqb_eq; exact CLR | apply Z.eqb_neq; exact CLR]). cbn [negb].
unfold set_lacing, stream_cells, wz. cbn [os_body_data os_body os_body_storage os_body_fill os_body_returned os_lacing_vals os_lacing os_granule_vals os_granules
os_lacing_storage os_lacing_fill os_lacing_packet os_lacing_returned os_header_fill os_e_o_s os_b_o_s os_serialno os_pageno os_packetno os_granulepos].
rewrite ?Els, ?Elf, ?Elp, ?Elr, ?Ebs, ?El.
split; [lazymatch goal with OSx : rw_cells rsegs _ A _ |- _ => exact OSx end|].
split; [exact BODY'|]. split; [exact BLEN|]. split; [exact BPRE|].
split; [exact LAC|]. split; [unfold wpre, zdrop; rewrite skipn_all2 by lia; cbn; split; [reflexivity| lia]|]. split; [exact LLEN|].
split; [exact GRA|]. split; [exact GLEN|].
split; [exact FR|]. split; [exact HS'|]. split; [| exact ST]. unfold page_cells, wz. exact OG'.
+
zstep. zstep. zstep. zstep. zstep. rewrite !Z.shiftl_mul_pow2 by lia. change (2^2) with 4.
pose proof (u32arr_u8 _ _ _ LAC) as LACB. clear LAC.
zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
call (memmove_fwd_spec _ (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp _ _ _ _ _ (Z_to_bv 64 L) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mx
L (4 * os_lacing_returned os) (4 * (os_lacing_fill os - os_lacing_returned os)) (u32s lws)) end.
all: try reflexivity. all: try (f_equal; (clear - os L gws lws F7 CE CLR I2 I1; lia)). all: try (rewrite ?u32s_length; lia).
all: try exact LACB. all: try assumption.
rename POST into LACB2. change X1fe.rsegs with rsegs in LACB2.
lazymatch goal with H0 : mem_inv X1fe.rsegs ?mm |- _ => change X1fe.rsegs with rsegs in H0 end.
replace (Z.to_nat (4 * (os_lacing_fill os - os_lacing_returned os))) with (4 * Z.to_nat (os_lacing_fill os - os_lacing_returned os))%nat in LACB2 by lia.
replace (Z.to_nat (4 * os_lacing_returned os)) with (4 * Z.to_nat (os_lacing_returned os))%nat in LACB2 by lia.
rewrite u32_move in LACB2 by lia. apply u8_u32arr in LACB2. rename LACB2 into LAC.
remember (firstn (Z.to_nat (os_lacing_fill os - os_lacing_returned os)) (skipn (Z.to_nat (os_lacing_returned os)) lws) ++ skipn (Z.to_nat (os_lacing_fill os - os_lacing_returned os)) lws) as lws2 eqn:Elws2.
assert (LLEN2 : Z.of_nat (length lws2) = ls) by (rewrite Elws2, app_length, firstn_length_le, skipn_length by (rewrite skipn_length; lia); lia).

zstep. zstep. zstep. zstep. zstep. zstep. rewrite !Z.shiftl_mul_pow2 by lia. change (2^3) with 8.
pose proof (u64arr_u8 _ _ _ GRA) as GRAB. clear GRA.
zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
call (memmove_fwd_spec _ (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp _ _ _ _ _ (Z_to_bv 64 Gv) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mx
Gv (8 * os_lacing_returned os) (8 * (os_lacing_fill os - os_lacing_returned os)) (u64s gws)) end.
all: try reflexivity. all: try (f_equal; lia). all: try (rewrite ?u64s_length; lia).
all: try exact GRAB. all: try assumption.
rename POST into GRAB2. change X1fe.rsegs with rsegs in GRAB2.
lazymatch goal with H0 : mem_inv X1fe.rsegs ?mm |- _ => change X1fe.rsegs with rsegs in H0 end.
replace (Z.to_nat (8 * (os_lacing_fill os - os_lacing_returned os))) with (8 * Z.to_nat (os_lacing_fill os - os_lacing_returned os))%nat in GRAB2 by lia.
replace (Z.to_nat (8 * os_lacing_returned os)) with (8 * Z.to_nat (os_lacing_returned os))%nat in GRAB2 by lia.
rewrite u64_move in GRAB2 by lia. apply u8_u64arr in GRAB2. rename GRAB2 into GRA.
remember (firstn (Z.to_nat (os_lacing_fill os - os_lacing_returned os)) (skipn (Z.to_nat (os_lacing_returned os)) gws) ++ skipn (Z.to_nat (os_lacing_fill os - os_lacing_returned os)) gws) as gws2 eqn:Egws2 in GRA.
assert (GLEN2 : Z.of_nat (length gws2) = ls) by (rewrite Egws2, app_length, firstn_length_le, skipn_length by (rewrite skipn_length; lia); lia).
assert (LPRE2 : wpre (zdrop (os_lacing_returned os) (os_lacing os)) lws2).
{ rewrite Elws2. unfold zdrop. replace (Z.to_nat (os_lacing_fill os - os_lacing_returned os)) with (length (os_lacing os) - Z.to_nat (os_lacing_returned os))%nat by (clear - gws2 lws2 LL I1 bodybytes' gws lws osb LFILL HL LENH os hs shdr og Gv L Bd Dsy; lia).
apply wpre_move; [exact LPRE| lia]. }

zstep.

zstep. zstep. zstep.
lstep. lstep. lstep.
apply evt_done. unfold prologue_post. unfold hideP in BODY, HS, OG, MU, WM.
lazymatch type of MUl with munch ?Wl m ?mf =>
pose proof (munch_trans _ _ _ _ MU (munch_weaken Wl W m mf ltac:(unfold sub_fp; cbn [outside]; intros; (clear - H x26 gws2 lws2 LL bodybytes' gws lws osb sp os shdr Gv L Bd A; lia)) MUl)) as MU';
pose proof (wmono_trans rsegs _ _ _ WM WMl) as WM';
unfold hideP in SEP_BL, SEP_BG;
pose proof (u8arr_transport rsegs Wl m mf Bd bodybytes' BODY MUl WMl ltac:(cbn [disjoint_from]; (clear - gws2 lws2 LL BLEN bodybytes' gws lws osb SEP_BG SEP_BL SEP_fB SPA LOSP HL LENH sp os hs shdr og lo Gv L Bd Dsy A; lia))) as BODY'; clear SEP_BL SEP_BG;
unfold hideP in SEP_HL, SEP_HG;
pose proof (bytes_at_transport rsegs Wl m mf _ hs HS MUl ltac:(cbn [disjoint_from]; (clear - GLEN2 gws2 lws2 LL bodybytes' gws lws osb SEP_HG SEP_HL SEP_LG SEP_Hf SPA LOSP HL LENH sp os hs shdr og lo Gv L Bd Dsy A; lia))) as HS'; clear SEP_HL SEP_HG;
unfold hideP in SEP_AG;
pose proof (rw_cells_transport rsegs Wl m mf G _ OG MUl WMl ltac:(cbn [disjoint_from cells_size csize Nat.add]; (clear - gws2 lws2 LL bodybytes' gws lws osb SEP_fG SEP_fL SEP_AG SPG SPA LOSP HL LENH sp os hs shdr og lo Gv L Bd Dsy G A; lia))) as OG'
end.
sf_eexists 18%nat. lazymatch goal with |- context [MS _ _ _ _ _ ?mx _ = _] => exists mx end. first [ unshelve sf_eexists 4%nat; [ exact (j0) | exact (bodybytes') | exact (lws2) | exact (gws2) | ] | sf_fb; exists j0, bodybytes', lws2, gws2 ].
split; [reflexivity|]. split; [exact MU'|]. split; [exact WM'|]. split; [assumption|].
rewrite EPR. unfold ret_lacing. rewrite El, Els, Elf, Elp, Elr. replace (os_lacing_returned os =? 0) with false by (symmetry; first [apply Z.eqb_eq; exact CLR | apply Z.eqb_neq; exact CLR]). cbn [negb].
unfold set_lacing, stream_cells, wz. cbn [os_body_data os_body os_body_storage os_body_fill os_body_returned os_lacing_vals os_lacing os_granule_vals os_granules
os_lacing_storage os_lacing_fill os_lacing_packet os_lacing_returned os_header_fill os_e_o_s os_b_o_s os_serialno os_pageno os_packetno os_granulepos].
rewrite ?Els, ?Elf, ?Elp, ?Elr, ?Ebs, ?El.
split; [lazymatch goal with OSx : rw_cells rsegs _ A _ |- _ => exact OSx end|].
split; [exact BODY'|]. split; [exact BLEN|]. split; [exact BPRE|].
split; [exact LAC|]. split; [exact LPRE2|]. split; [exact LLEN2|].
split; [exact GRA|]. split; [exact GLEN2|].
split; [exact FR|]. split; [exact HS'|]. split; [| exact ST]. unfold page_cells, wz. exact OG'.
Qed.

Lemma pi_bclean : forall m0 m (lws gws : list word) bodybytes (j0 : list byte) (v25 v22 : Z)
(x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
0 <= v25 < 2^64 -> 0 <= v22 < 2^64 -> Z_to_bv 64 (Z.lor v25 v22) = Z_to_bv 64 (ogg_page_serialno hdr) ->
munch W m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
rw_cells rsegs m A (stream_cells Bd L Gv shdr os) ->
u8arr rsegs m Bd bodybytes -> Z.of_nat (length bodybytes) = bs -> body_pre (os_body os) bodybytes ->
u32arr rsegs m L lws -> wpre (os_lacing os) lws -> Z.of_nat (length lws) = ls ->
u64arr rsegs m Gv gws -> Z.of_nat (length gws) = ls ->
FRAME m (LOC j0) -> bytes_at rsegs m H hs -> rw_cells rsegs m G (page_cells Dsy og) -> stk rsegs m lo (bv_unsigned sp + -144) ->
evt rsegs (prologue_post m0)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp x5 x6 x7 (Z_to_bv 64 A) (Z_to_bv 64 (os_lacing_returned os))
(Z_to_bv 64 Bd) (Z_to_bv 64 (os_body_returned os)) x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (-1)) (Z_to_bv 64 (pg_body_len og)) (Z_to_bv 64 (H + pg_header_len og)) (Z_to_bv 64 H) (Z_to_bv 64 v22)
(Z_to_bv 64 (znth hdr 19)) (Z_to_bv 64 (znth hdr 4)) (Z_to_bv 64 v25) (Z_to_bv 64 nseg) (Z_to_bv 64 (znth hdr 20)) x28 x29 x30 x31)
F (Z_to_bv 64 0x3091c) fc None m (seg_rom rsegs)).
Proof.
intros until x31. intros Hv25 Hv22 ESER MU WM MI OS BODY BLEN BPRE LAC LPRE LLEN GRA GLEN FR HS OG ST.
unfold page_cells, wz in OG. pose proof (rw_cells_bound _ _ _ _ OG) as GGB. cbn [cells_size csize Nat.add] in GGB.
hide SEP_AG. hide SEP_HL. hide SEP_HG. hide SEP_BL. hide SEP_BG. hide SEP_LG. hide SEP_HB. hide HS. hide OG. hide MU. hide WM. hide LAC. hide GRA.
pose proof FOK as sfP_; first [ sf_destruct 12%nat sfP_ as F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 | sf_fb; destruct sfP_ as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12) ]. unfold int31 in *.
pose proof BINV as (B1 & B2 & B3). unfold zlength in BFILL. pose proof BPRE as [BP1 BP2].
pose proof (rw_cells_bound _ _ _ _ OS) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof (byte_range (nth (Z.to_nat 19) hs (Z_to_bv 8 0))) as H19. rewrite <- (znth_ubytes hs 19) in H19 by lia.
pose proof (byte_range (nth (Z.to_nat 20) hs (Z_to_bv 8 0))) as H20. rewrite <- (znth_ubytes hs 20) in H20 by lia.
pose proof (byte_range (nth (Z.to_nat 4) hs (Z_to_bv 8 0))) as H4. rewrite <- (znth_ubytes hs 4) in H4 by lia.
unfold stream_cells, wz in OS. cbn [app] in FR.
pose proof (munch_refl [(bv_unsigned sp + -144, bv_unsigned sp); (A, A + 408); (Bd, Bd + bs)] m) as MUl. pose proof (wmono_refl rsegs m) as WMl.

zstep. if_cases CBR; zify_cond CBR; rewrite ?unsigned_lit in CBR by lia.
-

zstep. rewrite ESER.
unfold hideP in MU, WM, LAC, GRA, HS, OG.
lazymatch type of MUl with munch ?Wl m ?mf =>
pose proof (munch_trans _ _ _ _ MU (munch_weaken Wl W m mf ltac:(unfold sub_fp; cbn [outside]; intros; lia) MUl)) as MU';
pose proof (wmono_trans rsegs _ _ _ WM WMl) as WM';
unfold hideP in SEP_BL, SEP_BG;
pose proof (u32arr_transport rsegs Wl m mf L lws LAC MUl WMl ltac:(cbn [disjoint_from]; lia)) as LAC';
pose proof (u64arr_transport rsegs Wl m mf Gv gws GRA MUl WMl ltac:(cbn [disjoint_from]; lia)) as GRA'; hide SEP_BL; hide SEP_BG;
unfold hideP in SEP_HB;
pose proof (bytes_at_transport rsegs Wl m mf _ hs HS MUl ltac:(cbn [disjoint_from]; lia)) as HS'; hide SEP_HB;
unfold hideP in SEP_AG;
pose proof (rw_cells_transport rsegs Wl m mf G _ OG MUl WMl ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)) as OG'; hide SEP_AG
end.
eapply (pi_lclean m0 _ os lws gws bodybytes j0); try exact MU'; try exact WM'; try exact LAC'; try exact GRA'; try exact HS'; try exact OG'; try eassumption; try reflexivity.
all: try (unfold stream_fields_ok, int31 in *; cbn; lia).
all: try (rewrite pagein_returned_eq; unfold ret_body; replace (os_body_returned os =? 0) with true by (symmetry; apply Z.eqb_eq; exact CBR); reflexivity).
-
zstep. zstep. replace (os_body_fill os + - os_body_returned os) with (os_body_fill os - os_body_returned os) by lia.
lstep.
zstep. if_cases CBF; zify_cond CBF; rewrite ?unsigned_lit in CBF by lia.
+
lstep.
pose (bodybytes2 := bodybytes).
assert (BLEN2 : Z.of_nat (length bodybytes2) = bs) by exact BLEN.
assert (BODY2 : u8arr rsegs _ Bd bodybytes2) by exact BODY || idtac.

zstep. rewrite ESER.
unfold hideP in MU, WM, LAC, GRA, HS, OG.
lazymatch type of MUl with munch ?Wl m ?mf =>
pose proof (munch_trans _ _ _ _ MU (munch_weaken Wl W m mf ltac:(unfold sub_fp; cbn [outside]; intros; (clear - H x BP2 bodybytes gws lws sp os shdr Gv L Bd A; lia)) MUl)) as MU';
pose proof (wmono_trans rsegs _ _ _ WM WMl) as WM';
unfold hideP in SEP_BL, SEP_BG;
pose proof (u32arr_transport rsegs Wl m mf L lws LAC MUl WMl ltac:(cbn [disjoint_from]; (clear - bodybytes2 BP2 GGB LLEN BLEN bodybytes gws lws SEP_BL SEP_fL SEP_fB SPA LOSP HL LENH sp os hs shdr lo Gv L Bd G A; lia))) as LAC';
pose proof (u64arr_transport rsegs Wl m mf Gv gws GRA MUl WMl ltac:(cbn [disjoint_from]; (clear - bodybytes2 BP2 GGB GLEN BLEN bodybytes gws lws SEP_BG SEP_fG SEP_fB SPA LOSP HL LENH sp os hs shdr lo Gv L Bd G A; lia))) as GRA'; hide SEP_BL; hide SEP_BG;
unfold hideP in SEP_HB;
pose proof (bytes_at_transport rsegs Wl m mf _ hs HS MUl ltac:(cbn [disjoint_from]; (clear - bodybytes2 BP2 GGB BLEN bodybytes gws lws SEP_HB SEP_Hf SEP_fB SPA LOSP HL LENH sp os hs shdr og lo Gv L Bd Dsy G A; lia))) as HS'; hide SEP_HB;
unfold hideP in SEP_AG;
pose proof (rw_cells_transport rsegs Wl m mf G _ OG MUl WMl ltac:(cbn [disjoint_from cells_size csize Nat.add]; (clear - bodybytes2 BP2 GGB bodybytes gws lws SEP_fB SEP_AG SPG SPA LOSP HL LENH sp os hs shdr lo Gv L Bd G A; lia))) as OG'; hide SEP_AG
end.
eapply (pi_lclean m0 _ (set_body os (ztake (os_body_fill os - os_body_returned os) (zdrop (os_body_returned os) (os_body os))) bs (os_body_fill os - os_body_returned os) 0) lws gws bodybytes2 j0); try exact MU'; try exact WM'; try exact LAC'; try exact GRA'; try exact HS'; try exact OG'; try eassumption; try reflexivity.
all: try (unfold stream_fields_ok, int31 in *; cbn; lia).
all: try (rewrite pagein_returned_eq; unfold ret_body; replace (os_body_returned os =? 0) with false by (symmetry; apply Z.eqb_neq; exact CBR); reflexivity).
all: try (unfold body_pre, set_body; cbn [os_body]; unfold ztake; replace (Z.to_nat (os_body_fill os - os_body_returned os)) with 0%nat by lia;
repeat (lazymatch goal with |- context [firstn 0 ?l] => change (firstn 0 l) with (@nil Z) end); cbn [length]; split; [reflexivity| lia]).
+
zstep. zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
call (memmove_fwd_spec _ (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp _ _ _ _ _ (Z_to_bv 64 Bd) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mx
Bd (os_body_returned os) (os_body_fill os - os_body_returned os) bodybytes) end.
all: try reflexivity. all: try (f_equal; lia). all: try lia.
all: try exact BODY. all: try assumption.
rename POST into BODY2. change X1fe.rsegs with rsegs in BODY2.
lazymatch goal with H0 : mem_inv X1fe.rsegs ?mm |- _ => change X1fe.rsegs with rsegs in H0 end.
pose proof (compact_prefix (os_body os) bodybytes (Z.to_nat (os_body_returned os)) (Z.to_nat (os_body_fill os - os_body_returned os)) BP1 ltac:(lia) BP2) as [BP1' BP2'].
remember (firstn (Z.to_nat (os_body_fill os - os_body_returned os)) (skipn (Z.to_nat (os_body_returned os)) bodybytes) ++ skipn (Z.to_nat (os_body_fill os - os_body_returned os)) bodybytes) as bodybytes2 eqn:Ebb2.
assert (BLEN2 : Z.of_nat (length bodybytes2) = bs) by (rewrite Ebb2, app_length, firstn_length_le, skipn_length by (rewrite skipn_length; lia); lia).
lstep.

zstep. rewrite ESER.
unfold hideP in MU, WM, LAC, GRA, HS, OG.
lazymatch type of MUl with munch ?Wl m ?mf =>
pose proof (munch_trans _ _ _ _ MU (munch_weaken Wl W m mf ltac:(unfold sub_fp; cbn [outside]; intros; lia) MUl)) as MU';
pose proof (wmono_trans rsegs _ _ _ WM WMl) as WM';
unfold hideP in SEP_BL, SEP_BG;
pose proof (u32arr_transport rsegs Wl m mf L lws LAC MUl WMl ltac:(cbn [disjoint_from]; lia)) as LAC';
pose proof (u64arr_transport rsegs Wl m mf Gv gws GRA MUl WMl ltac:(cbn [disjoint_from]; lia)) as GRA'; hide SEP_BL; hide SEP_BG;
unfold hideP in SEP_HB;
pose proof (bytes_at_transport rsegs Wl m mf _ hs HS MUl ltac:(cbn [disjoint_from]; lia)) as HS'; hide SEP_HB;
unfold hideP in SEP_AG;
pose proof (rw_cells_transport rsegs Wl m mf G _ OG MUl WMl ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)) as OG'; hide SEP_AG
end.
eapply (pi_lclean m0 _ (set_body os (ztake (os_body_fill os - os_body_returned os) (zdrop (os_body_returned os) (os_body os))) bs (os_body_fill os - os_body_returned os) 0) lws gws bodybytes2 j0); try exact MU'; try exact WM'; try exact LAC'; try exact GRA'; try exact HS'; try exact OG'; try eassumption; try reflexivity.
all: try (unfold stream_fields_ok, int31 in *; cbn; lia).
all: try (rewrite pagein_returned_eq; unfold ret_body; replace (os_body_returned os =? 0) with false by (symmetry; apply Z.eqb_neq; exact CBR); reflexivity).
all: try (unfold body_pre, set_body; cbn [os_body]; unfold ztake, zdrop; split; [exact BP1'| exact BP2']).
Qed.

Lemma pi_prologue : forall m (lws gws : list word) bodybytes
(t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) ->
rw_cells rsegs m A (stream_cells Bd L Gv shdr os) ->
u8arr rsegs m Bd bodybytes -> Z.of_nat (length bodybytes) = bs -> body_pre (os_body os) bodybytes ->
u32arr rsegs m L lws -> wpre (os_lacing os) lws -> Z.of_nat (length lws) = ls ->
u64arr rsegs m Gv gws -> Z.of_nat (length gws) = ls ->
bytes_at rsegs m H hs -> rw_cells rsegs m G (page_cells Dsy og) ->
evt rsegs (prologue_post m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 G) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x30860) fc None m (seg_rom rsegs)).
Proof.
intros until t6. intros MI ST OS BODY BLEN BPRE LAC LPRE LLEN GRA GLEN HS OG.
unfold page_cells, wz in OG. pose proof (rw_cells_bound _ _ _ _ OG) as GGB. cbn [cells_size csize Nat.add] in GGB.
hide SEP_AG. hide SEP_HL. hide SEP_HG. hide SEP_BL. hide SEP_BG. hide SEP_LG. hide SEP_HB. hide BODY. hide LAC. hide GRA.
pose proof FOK as sfP_; first [ sf_destruct 12%nat sfP_ as F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 | sf_fb; destruct sfP_ as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12) ]. unfold int31 in *.
pose proof BINV as (B1 & B2 & B3). pose proof INV as (I1 & I2 & I3).
unfold stream_cells, wz in OS. pose proof (rw_cells_bound _ _ _ _ OS) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof HS as (HB0 & HB1 & HB).
pose proof (munch_refl W m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)] m) as MUl. pose proof (wmono_refl rsegs m) as WMl.
carve_frame 144%nat ST.

zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.

zstep. zstep. zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
pose proof (bytes_at_read1 rsegs mx H hs 4 _ HS ltac:(lia) ltac:(lia) eq_refl) as R4;
pose proof (bytes_at_read1 rsegs mx H hs 5 _ HS ltac:(lia) ltac:(lia) eq_refl) as R5 end.
zstep. zstep. clear R4 R5.

zstep. zstep. zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
call (ogg_page_granulepos_spec _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mx G Dsy og hs) end.
all: try reflexivity. all: try exact OG. all: try exact HS. all: try lia. all: try assumption.
subst.

zstep. zstep. if_cases CA; zify_cond CA; rewrite ?unsigned_lit, ?land_ones64 in CA by lia. 1: exfalso; lia.

zstep. zstep. zstep. if_cases CB0; zify_cond CB0; rewrite ?unsigned_lit, ?land_ones64 in CB0 by lia. 1: exfalso; lia.

zstep. zstep.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
pose proof (bytes_at_read1 rsegs mx H hs 14 _ HS ltac:(lia) ltac:(lia) eq_refl) as R14;
pose proof (bytes_at_read1 rsegs mx H hs 15 _ HS ltac:(lia) ltac:(lia) eq_refl) as R15;
pose proof (bytes_at_read1 rsegs mx H hs 16 _ HS ltac:(lia) ltac:(lia) eq_refl) as R16;
pose proof (bytes_at_read1 rsegs mx H hs 17 _ HS ltac:(lia) ltac:(lia) eq_refl) as R17;
pose proof (bytes_at_read1 rsegs mx H hs 18 _ HS ltac:(lia) ltac:(lia) eq_refl) as R18 end.
zstep. zstep. zstep. zstep. zstep. clear R14 R15 R16 R17 R18.

zstep.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
pose proof (bytes_at_read1 rsegs mx H hs 19 _ HS ltac:(lia) ltac:(lia) eq_refl) as R19;
pose proof (bytes_at_read1 rsegs mx H hs 20 _ HS ltac:(lia) ltac:(lia) eq_refl) as R20;
pose proof (bytes_at_read1 rsegs mx H hs 21 _ HS ltac:(lia) ltac:(lia) eq_refl) as R21 end.
zstep. zstep. zstep. clear R19 R20 R21.

zstep.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
pose proof (bytes_at_read1 rsegs mx H hs 26 _ HS ltac:(lia) ltac:(lia) eq_refl) as R26 end.
zstep. clear R26.

zstep. zstep. zstep. zstep. zstep. zstep. zstep.

rewrite <- !(znth_ubytes hs) in FR by lia.
rewrite <- !(znth_ubytes hs) by lia.
lazymatch goal with |- context [Z_to_bv 64 (bv_swrap 32 ?e)] => rewrite <- (Z_to_bv_mod64 (bv_swrap 32 e)) end.
lazymatch goal with |- context [Z_to_bv 64 (Z.lor (Z.lor ?a ?b) ?c)] => rewrite <- (Z_to_bv_mod64 (Z.lor (Z.lor a b) c)) end.
unfold hideP in BODY, LAC, GRA.
lazymatch type of MUl with munch ?Wl m ?mf =>
pose proof (u8arr_transport rsegs Wl m mf Bd bodybytes BODY MUl WMl ltac:(cbn [disjoint_from]; lia)) as BODY';
pose proof (u32arr_transport rsegs Wl m mf L lws LAC MUl WMl ltac:(cbn [disjoint_from]; lia)) as LAC';
pose proof (u64arr_transport rsegs Wl m mf Gv gws GRA MUl WMl ltac:(cbn [disjoint_from]; lia)) as GRA'
end.
eapply (pi_bclean m _ lws gws bodybytes); try exact MU; try exact WM; try exact OS; try exact BODY'; try exact LAC'; try exact GRA'; try exact FR; try eassumption.
- apply Z.mod_pos_bound. lia.
- apply Z.mod_pos_bound. lia.
- rewrite !znth_ubytes by (clear - GB GGB bodybytes gws lws HL LENH hs shdr G A; lia). apply serialno_pieces. lia.
Qed.
End PIE.
