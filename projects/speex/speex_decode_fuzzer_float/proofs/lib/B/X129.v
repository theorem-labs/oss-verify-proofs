(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1ch X1cg X1dk X1cr X1cs X1dg X1df X1ck X1co.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X05o X05p X05q X05l.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X0yr X12b X0wh X0yt X0z5 X12a X127 X128.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac tlia ::= (try unfold BITS_SIZEOF in * ); tlia_one.
Local Ltac slia ::= (try unfold BITS_SIZEOF in * ); first [ exact I | lia | split; [lia|exact I] ].
Local Notation mem := (word -> option byte).

Ltac jx_cut_here pcJ :=
lazymatch goal with |- evt ?segs _ (MS ?R _ _ _ _ ?mc _) =>
let r := open_constr:(mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) in
unify R r;
lazymatch r with
| mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 _ ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20 ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?x29 ?x30 ?x31 =>
eapply (evt_cut segs (JX segs pcJ mc x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31))
end
end.

Ltac jx_cut_here6 pcJ v6 :=
lazymatch goal with |- evt ?segs _ (MS ?R _ _ _ _ ?mc _) =>
let r := open_constr:(mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) in
unify R r;
lazymatch r with
| mkR ?x1 ?x2 ?x3 ?x4 ?x5 _ ?x7 ?x8 ?x9 _ ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20 ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?x29 ?x30 ?x31 =>
eapply (evt_cut segs (JX segs pcJ mc x1 x2 x3 x4 x5 v6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31))
end
end.

Definition scb_inner_post (zra zsp zgp ztp zt0 zt1 zs0 zs1 za2 za3 za4 za5 za7 zs2 zs3 zs4 zs5 zs6 zs7 zs9 zs10 zs11 zt5 zt6 : word) (INN : Z) (mI : mem) : machine_state -> Prop :=
fun ms' => exists t2' a0' a1' a6' t3' t4' F' fc' m' (ws : list word),
ms' = MS (mkR zra zsp zgp ztp zt0 zt1 t2' zs0 zs1 a0' a1' za2 za3 za4 za5 a6' za7 zs2 zs3 zs4 zs5 zs6 zs7 (Z_to_bv 64 SHB) zs9 zs10 zs11 t3' t4' zt5 zt6)
F' (Z_to_bv 64 0xb26ac) fc' None m' (seg_rom bsegs)
/\ munch [(INN, INN + 160)] mI m' /\ wmono bsegs mI m' /\ mem_inv bsegs m'
/\ frm0 fc' /\ rw_cells bsegs m' INN (f32 ws) /\ length ws = 40%nat.

Lemma scb_inner : forall (INN CDB CN ssz row e : Z) (CD : list byte) (mI : mem) (zra zsp zgp ztp zs0 zs1 za2 za4 zs3 zs4 zs5 zs6 zs7 zs10 zt5 zt6 : word),
INN mod 4 = 0 -> 0 < INN -> aobj bsegs mI INN 160 -> offsh [(INN, INN + 160)] ->
0 < CDB -> aobj bsegs mI CDB CN -> Z.of_nat (length CD) = CN -> CDB + CN <= INN ->
1 <= ssz <= 20 -> 0 <= row -> row + ssz <= CN -> CN <= 5120 -> 0 <= e -> e + ssz <= 40 ->
forall (k : nat) (rest done : list word) (x : word) (j off : Z) (yt2 ya0 ya1 yt3 yt4 : word) (F1 : bvmap 5 word) fc mc,
Z.of_nat (S k) = ssz - j -> 0 <= j -> Z.of_nat (length done) = e + j -> off = 4 * Z.of_nat (length done) -> (length done + 1 + length rest = 40)%nat ->
u8ro bsegs mc CDB CD ->
frm0 fc -> mem_inv bsegs mc -> munch [(INN, INN + 160)] mI mc -> wmono bsegs mI mc ->
rw_cells bsegs mc INN (f32 done) -> rw_cells bsegs mc (INN + off) (f32 (x :: rest)) ->
evt bsegs (scb_inner_post zra zsp zgp ztp (Z_to_bv 64 row) (Z_to_bv 64 e) zs0 zs1 za2 (Z_to_bv 64 1) za4 (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 INN) zs3 zs4 zs5 zs6 zs7 (Z_to_bv 64 ssz) zs10 (Z_to_bv 64 CDB) zt5 zt6 INN mI)
(MS (mkR zra zsp zgp ztp (Z_to_bv 64 row) (Z_to_bv 64 e) yt2 zs0 zs1 ya0 ya1 za2 (Z_to_bv 64 1) za4 (Z_to_bv 64 1) (Z_to_bv 64 j) (Z_to_bv 64 0)
(Z_to_bv 64 INN) zs3 zs4 zs5 zs6 zs7 (Z_to_bv 64 SHB) (Z_to_bv 64 ssz) zs10 (Z_to_bv 64 CDB) yt3 yt4 zt5 zt6)
F1 (Z_to_bv 64 0xb25b8) fc None mc (seg_rom bsegs)).
Proof.
intros INN CDB CN ssz row e CD mI zra zsp zgp ztp zs0 zs1 za2 za4 zs3 zs4 zs5 zs6 zs7 zs10 zt5 zt6 N4 N0 OBQ OF C0 OBC LCD SEP HSS R0 R1 CNB E0 E1 k.
pose proof OBQ as (OQ0 & OQ1 & _). pose proof OBC as (OC0 & OC1 & _). unfold APP_TOP in *.
induction k as [|k IH]; intros rest done x j off yt2 ya0 ya1 yt3 yt4 F1 fc mc Hk Hj HD Hoff HN RO FRM MI MU WM DONE X;
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof (rw_cells_bound _ _ _ _ DONE) as BD; rewrite cells_size_f32 in BD.
2:{
destruct rest as [|x2 rest]; [cbn [length] in HN; lia|]. cbn [length] in HN, BX.
rewrite f32_cons in X. chunk_uncons X as X1.
assert (NTH : nth_error CD (Z.to_nat (row + j)) = Some (nth (Z.to_nat (row + j)) CD (Z_to_bv 8 0))) by (apply nth_error_nth'; lia).
bato 0xb25f8.
pose proof (u8ro_read bsegs mc CDB CD (row + j) _ (wa (CDB + (row + j + 0))) RO NTH ltac:(lia) ltac:(f_equal; lia)) as RD. clear NTH.
astep. chk_merge OBC 1.
bato 0xb2638.
replace (INN + (e + j + 0) * 4) with (INN + off) by lia.
assert (AL : (INN + off) mod 4 = 0) by (clear - N4 Hoff; Z.div_mod_to_equations; lia).
bato 0xb2650.
astep. chk_merge OBQ 4.
bato 0xb265c. astep. chk_merge OBQ 4.
bato 0xb2678. astep.
rewrite swrap32_small by lia. sh_if.
chunk_snoc DONE X1. rewrite f32_snoc in DONE.
replace (INN + off + 4) with (INN + (off + 4)) in * by lia.
eapply (IH rest (done ++ [_]) x2 (j + 1) (off + 4)); try eassumption.
all: try (rewrite ?length_app; cbn [length] in *; lia).
}
{
pose proof X as XF. rewrite f32_cons in X. chunk_uncons X as X1. clear XF.
assert (NTH : nth_error CD (Z.to_nat (row + j)) = Some (nth (Z.to_nat (row + j)) CD (Z_to_bv 8 0))) by (apply nth_error_nth'; lia).
bato 0xb25f8.
pose proof (u8ro_read bsegs mc CDB CD (row + j) _ (wa (CDB + (row + j + 0))) RO NTH ltac:(lia) ltac:(f_equal; lia)) as RD. clear NTH.
astep. chk_merge OBC 1.
bato 0xb2638.
replace (INN + (e + j + 0) * 4) with (INN + off) by lia.
assert (AL : (INN + off) mod 4 = 0) by (clear - N4 Hoff; Z.div_mod_to_equations; lia).
bato 0xb2650.
astep. chk_merge OBQ 4.
bato 0xb265c. astep. chk_merge OBQ 4.
bato 0xb2678. astep.
rewrite swrap32_small by lia. sh_if.
bato 0xb26ac.
chunk_snoc DONE X1. rewrite f32_snoc in DONE.
replace (INN + off + 4) with (INN + 4 * Z.of_nat (length (done ++ [ltac:(lazymatch type of DONE with rw_cells _ _ _ (f32 (_ ++ [?w])) => exact w end)]))) in X
by (rewrite length_app; cbn [length]; lia).
pose proof (f32_join bsegs _ INN _ _ DONE X) as ALL.
unfold scb_inner_post. finish; [ exact ALL | ].
rewrite !length_app. cbn [length]. lia.
}
Qed.

Definition scb_outer_post (zra zsp zgp ztp zs0 za3 za4 za5 zs2 zs3 zs4 zs5 zs6 zs7 zs9 zs10 zs11 zt5 zt6 : word) (FB INN : Z) (mI : mem) : machine_state -> Prop :=
fun ms' => exists t0' t1' t2' a0' a1' a2' a6' a7' t3' t4' F' fc' m' (ws : list word),
ms' = MS (mkR zra zsp zgp ztp t0' t1' t2' zs0 (Z_to_bv 64 FB) a0' a1' a2' za3 za4 za5 a6' a7' zs2 zs3 zs4 zs5 zs6 zs7 (Z_to_bv 64 SHB) zs9 zs10 zs11 t3' t4' zt5 zt6)
F' (Z_to_bv 64 0xb26e0) fc' None m' (seg_rom bsegs)
/\ munch [(INN, INN + 160)] mI m' /\ wmono bsegs mI m' /\ mem_inv bsegs m'
/\ frm0 fc' /\ rw_cells bsegs m' INN (f32 ws) /\ length ws = 40%nat.

Lemma scb_outer : forall (SP FB IND SGN INN CDB ssz sbits nbz hs : Z) (CD : list byte) (mI : mem) (zra zsp zgp ztp zs0 zs3 zs5 zs6 zs7 zs10 zt5 zt6 : word)
(c0 c16 c64 : word) (j8 j72 j80 : list byte) (r11 r10 r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra : word),
FB = SP + 192 -> IND = SP + 128 -> SGN = SP + 32 -> SP mod 4 = 0 -> 0 <= SP -> SP + 384 < 2^63 ->
1 <= ssz <= 20 -> 1 <= sbits <= 8 -> 1 <= nbz <= 8 -> ssz * nbz = 40 ->
INN mod 4 = 0 -> 0 < INN -> aobj bsegs mI INN 160 -> offsh [(INN, INN + 160)] -> (INN + 160 <= SP \/ SP + 384 <= INN) ->
0 < CDB -> aobj bsegs mI CDB (2 ^ sbits * ssz) -> Z.of_nat (length CD) = 2 ^ sbits * ssz -> CDB + 2 ^ sbits * ssz <= INN -> CDB + 2 ^ sbits * ssz <= SP ->
aobj bsegs mI IND (4 * nbz) -> aobj bsegs mI SGN (4 * nbz) ->
forall (irest srest : list word) (iw sw : word) (done rest : list word) (i e off offi : Z) (yt0 yt1 yt2 ya0 ya1 ya6 ya7 yt3 yt4 : word) (F1 : bvmap 5 word) fc mc,
i + Z.of_nat (S (length irest)) = nbz -> 0 <= i -> offi = 4 * i -> length srest = length irest ->
e = ssz * i -> Z.of_nat (length done) = e -> off = 4 * Z.of_nat (length done) ->
Z.of_nat (length rest) = ssz * Z.of_nat (S (length irest)) -> (length done + length rest = 40)%nat ->
Forall (wbnd (2 ^ sbits)) (iw :: irest) -> Forall (wbnd 2) (sw :: srest) ->
rw_cells bsegs mc FB (scb_frameL hs nbz IND SGN c0 c16 c64 j8 j72 j80 r11 r10 r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra) ->
rw_cells bsegs mc (IND + offi) (f32 (iw :: irest)) -> rw_cells bsegs mc (SGN + offi) (f32 (sw :: srest)) ->
u8ro bsegs mc CDB CD ->
rw_cells bsegs mc INN (f32 done) -> rw_cells bsegs mc (INN + off) (f32 rest) ->
frm0 fc -> mem_inv bsegs mc -> munch [(INN, INN + 160)] mI mc -> wmono bsegs mI mc ->
evt bsegs (scb_outer_post zra zsp zgp ztp zs0 (Z_to_bv 64 1) (Z_to_bv 64 0x23718) (Z_to_bv 64 1) (Z_to_bv 64 INN) zs3 (Z_to_bv 64 SGN) zs5 zs6 zs7 (Z_to_bv 64 ssz) zs10 (Z_to_bv 64 CDB) zt5 zt6 FB INN mI)
(MS (mkR zra zsp zgp ztp yt0 yt1 yt2 zs0 (Z_to_bv 64 FB) ya0 ya1 (Z_to_bv 64 i) (Z_to_bv 64 1) (Z_to_bv 64 0x23718) (Z_to_bv 64 1) ya6 ya7
(Z_to_bv 64 INN) zs3 (Z_to_bv 64 SGN) zs5 zs6 zs7 (Z_to_bv 64 SHB) (Z_to_bv 64 ssz) zs10 (Z_to_bv 64 CDB) yt3 yt4 zt5 zt6)
F1 (Z_to_bv 64 0xb2534) fc None mc (seg_rom bsegs)).
Proof.
intros SP FB IND SGN INN CDB ssz sbits nbz hs CD mI zra zsp zgp ztp zs0 zs3 zs5 zs6 zs7 zs10 zt5 zt6 c0 c16 c64 j8 j72 j80 r11 r10 r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra
EFB EIND ESGN SP4 SP0 SPH HSS HSB HNB HSN N4 N0 OBN OF NAP C0 OBC LCD SEPC SEPS OBI OBS irest.
pose proof OBN as (ON0 & ON1 & _). pose proof OBC as (OC0 & OC1 & _). unfold APP_TOP in *.
assert (I4 : IND mod 4 = 0) by (clear - EIND SP4; Z.div_mod_to_equations; lia).
assert (S4 : SGN mod 4 = 0) by (clear - ESGN SP4; Z.div_mod_to_equations; lia).
assert (P2 : 2 <= 2 ^ sbits <= 256).
{ clear - HSB. split; [change 2 with (2 ^ 1) at 1| change 256 with (2 ^ 8)]; apply Z.pow_le_mono_r; lia. }
assert (CNB : 2 ^ sbits * ssz <= 5120) by (clear - P2 HSS; nia).
hide_disj.
induction irest as [|iw' irest IH]; intros srest iw sw done rest i e off offi yt0 yt1 yt2 ya0 ya1 ya6 ya7 yt3 yt4 F1 fc mc
Hi Hi0 Hoffi LSR He HD Hoff LREST LTOT FI FS FR IX SX RO DONE REST FRM MI MU WM.
2:{
destruct srest as [|sw' srest]; [cbn [length] in LSR; lia|].
apply Forall_cons_iff in FI. destruct FI as ((iv & -> & IVR) & FI).
apply Forall_cons_iff in FS. destruct FS as ((sv & -> & SVR) & FS).
cbn [length] in Hi, LSR, LREST.
unfold scb_frameL, scb_frame, NOTW in FR.
bato 0xb2540. astep.
replace (i * 4) with offi by lia.
rewrite f32_cons in SX. chunk_uncons SX as SX1. rewrite f32_cons in IX. chunk_uncons IX as IX1.
bato 0xb2550. astep. chk_merge OBS 4.
bato 0xb2578. astep. chk_merge OBI 4.
bato 0xb2580.
rewrite (sx32_small iv) by (unfold int31; lia).
assert (ROW : 0 <= iv * ssz /\ iv * ssz + ssz <= 2 ^ sbits * ssz) by (clear - IVR HSS P2; nia).
assert (EB : 0 <= ssz * i /\ ssz * i + ssz <= 40) by (clear - Hi Hi0 HSS HSN; nia).
bato 0xb2590.
assert (SV : sv = 0 \/ sv = 1) by lia.
jx_cut_here6 0xb25a4 (Z_to_bv 64 (ssz * i));
[ destruct SV as [-> | ->]; rewrite sx32_small by (unfold int31; lia); bato 0xb2594; rewrite ?unsigned_small64 by lia;
[ change (Z.b2z (0 <? 1)) with 1 | change (Z.b2z (1 <? 1)) with 0 ]; bato 0xb25a4; jx_done
| clear FRM; intros ? (? & ? & ? & -> & FRM) ].
bato 0xb25b8.
bnorm. rewrite !Z.add_0_r. bdec.
set (row := iv * ssz) in *. destruct ROW as (R0 & R1).
assert (EE : ssz * i = e) by (symmetry; exact He). rewrite EE in *. destruct EB as (E0 & E1).
assert (REM0 : 0 <= ssz * Z.of_nat (length irest)) by (apply Z.mul_nonneg_nonneg; lia).
destruct rest as [|wx wr]; [cbn [length] in LREST; lia|].
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mc _) =>
lazymatch type of MU with munch ?W ?m0 mc =>
pose proof (aobj_munch bsegs W m0 mc INN 160 OBN MU (shfree_of_aobj bsegs W m0 INN 160 OF OBN)) as OBNc;
pose proof (aobj_munch bsegs W m0 mc CDB _ OBC MU (shfree_of_aobj bsegs W m0 CDB _ OF OBC)) as OBCc;
pose proof (munch_refl [(INN, INN + 160)] mc) as MU0; pose proof (wmono_refl bsegs mc) as WM0;
eapply evt_cut; [ eapply (scb_inner INN CDB (2 ^ sbits * ssz) ssz row e CD mc) with (k := Z.to_nat (ssz - 1)) (rest := wr) (done := done) (x := wx) (j := 0) (off := off)
| clear MU0 WM0 OBNc OBCc DONE REST FRM; post_call segs mc ]
end end.
1: exact N4. 1: exact N0. 1: exact OBNc. 1: exact OF. 1: exact C0. 1: exact OBCc. 1: exact LCD. 1: exact SEPC. 1: exact HSS. 1: exact R0. 1: exact R1. 1: exact CNB. 1: exact E0. 1: exact E1.
1: lia. 1: lia. 1: lia. 1: exact Hoff. 1: (cbn [length] in LTOT |- *; lia).
1: exact RO. 1: eassumption. 1: eassumption. 1: exact MU0. 1: exact WM0. 1: exact DONE. 1: exact REST.
rename PC into FRM. rename PC0 into ALL. rename POST into LALL.
lazymatch type of ALL with rw_cells _ _ _ (f32 ?l) => rename l into ws end.
bato 0xb26b4. astep.
rewrite swrap32_small by lia. sh_if.
assert (KL : (length done + Z.to_nat ssz <= length ws)%nat) by lia.
destruct (f32_split bsegs _ INN ws (length done + Z.to_nat ssz) KL ALL) as (DONE' & REST').
assert (LD' : length (firstn (length done + Z.to_nat ssz) ws) = (length done + Z.to_nat ssz)%nat) by (apply firstn_length_le; exact KL).
assert (LR' : length (skipn (length done + Z.to_nat ssz) ws) = (length ws - (length done + Z.to_nat ssz))%nat) by (apply length_skipn).
set (done' := firstn (length done + Z.to_nat ssz) ws) in *. set (rest' := skipn (length done + Z.to_nat ssz) ws) in *. clearbody done' rest'. clear ALL.
replace (SGN + offi + 4) with (SGN + (offi + 4)) in * by lia. replace (IND + offi + 4) with (IND + (offi + 4)) in * by lia.
cbn [length] in LTOT, LREST.
eapply (IH srest iw' sw' done' rest' (i + 1) (e + ssz) (4 * Z.of_nat (length done + Z.to_nat ssz)) (offi + 4)).
1: lia. 1: lia. 1: lia. 1: lia. 1: lia. 1: lia.
1: (rewrite LD'; reflexivity).
1: lia.
1: lia.
1: exact FI. 1: exact FS.
1: (unfold scb_frameL, scb_frame, NOTW; exact FR).
1: exact IX. 1: exact SX. 1: exact RO. 1: exact DONE'. 1: exact REST'.
1: exact FRM. 1: assumption. 1: exact MU. 1: exact WM.
}
{
destruct srest as [|sw' srest]; [|cbn [length] in LSR; lia].
apply Forall_cons_iff in FI. destruct FI as ((iv & -> & IVR) & FI).
apply Forall_cons_iff in FS. destruct FS as ((sv & -> & SVR) & FS).
cbn [length] in Hi, LSR, LREST.
unfold scb_frameL, scb_frame, NOTW in FR.
bato 0xb2540. astep.
replace (i * 4) with offi by lia.
rewrite f32_cons, f32_nil in SX. rewrite f32_cons, f32_nil in IX.
bato 0xb2550. astep. chk_merge OBS 4.
bato 0xb2578. astep. chk_merge OBI 4.
bato 0xb2580.
rewrite (sx32_small iv) by (unfold int31; lia).
assert (ROW : 0 <= iv * ssz /\ iv * ssz + ssz <= 2 ^ sbits * ssz) by (clear - IVR HSS P2; nia).
assert (EB : 0 <= ssz * i /\ ssz * i + ssz <= 40) by (clear - Hi Hi0 HSS HSN; nia).
bato 0xb2590.
assert (SV : sv = 0 \/ sv = 1) by lia.
jx_cut_here6 0xb25a4 (Z_to_bv 64 (ssz * i));
[ destruct SV as [-> | ->]; rewrite sx32_small by (unfold int31; lia); bato 0xb2594; rewrite ?unsigned_small64 by lia;
[ change (Z.b2z (0 <? 1)) with 1 | change (Z.b2z (1 <? 1)) with 0 ]; bato 0xb25a4; jx_done
| clear FRM; intros ? (? & ? & ? & -> & FRM) ].
bato 0xb25b8.
bnorm. rewrite !Z.add_0_r. bdec.
set (row := iv * ssz) in *. destruct ROW as (R0 & R1).
assert (EE : ssz * i = e) by (symmetry; exact He). rewrite EE in *. destruct EB as (E0 & E1).
destruct rest as [|wx wr]; [cbn [length] in LREST; lia|].
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mc _) =>
lazymatch type of MU with munch ?W ?m0 mc =>
pose proof (aobj_munch bsegs W m0 mc INN 160 OBN MU (shfree_of_aobj bsegs W m0 INN 160 OF OBN)) as OBNc;
pose proof (aobj_munch bsegs W m0 mc CDB _ OBC MU (shfree_of_aobj bsegs W m0 CDB _ OF OBC)) as OBCc;
pose proof (munch_refl [(INN, INN + 160)] mc) as MU0; pose proof (wmono_refl bsegs mc) as WM0;
eapply evt_cut; [ eapply (scb_inner INN CDB (2 ^ sbits * ssz) ssz row e CD mc) with (k := Z.to_nat (ssz - 1)) (rest := wr) (done := done) (x := wx) (j := 0) (off := off)
| clear MU0 WM0 OBNc OBCc DONE REST FRM; post_call segs mc ]
end end.
1: exact N4. 1: exact N0. 1: exact OBNc. 1: exact OF. 1: exact C0. 1: exact OBCc. 1: exact LCD. 1: exact SEPC. 1: exact HSS. 1: exact R0. 1: exact R1. 1: exact CNB. 1: exact E0. 1: exact E1.
1: lia. 1: lia. 1: lia. 1: exact Hoff. 1: (cbn [length] in LTOT |- *; lia).
1: exact RO. 1: eassumption. 1: eassumption. 1: exact MU0. 1: exact WM0. 1: exact DONE. 1: exact REST.
rename PC into FRM. rename PC0 into ALL. rename POST into LALL.
bato 0xb26b4. astep.
rewrite swrap32_small by lia. sh_if.
bato 0xb26e0.
unfold scb_outer_post. finish; [ exact ALL | exact LALL ].
}
Qed.
