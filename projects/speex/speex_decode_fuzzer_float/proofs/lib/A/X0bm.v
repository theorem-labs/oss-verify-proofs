(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1ch X1cg X1cr X1cs X1dg X1df X1ck X1co.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p X05q X05l X082 X0bl.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac tlia ::= tlia_one.
Local Notation mem := (word -> option byte).

Definition scb_inner_post (zra zsp zgp ztp zs0 zs1 za2 za3 za4 za5 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs10 zs11 zt5 zt6 : word) (Q NZ : Z) (n : nat) (mI : mem) : machine_state -> Prop :=
fun ms' => exists t0' t1' t2' a0' a1' a6' a7' t3' t4' F' fc' m' (ws : list word),
ms' = MS (mkR zra zsp zgp ztp t0' t1' t2' zs0 zs1 a0' a1' za2 za3 za4 za5 a6' a7' zs2 zs3 zs4 zs5 zs6 zs7 zs8 (Z_to_bv 64 SHB) zs10 zs11 t3' t4' zt5 zt6)
F' (Z_to_bv 64 0xac9f0) fc' None m' (seg_rom asegs)
/\ munch [(Q, Q + NZ)] mI m' /\ wmono asegs mI m' /\ mem_inv asegs m'
/\ frm0 fc' /\ rw_cells asegs m' Q (f32 ws) /\ length ws = n.

Lemma scb_inner : forall (Q NZ : Z) (n : nat) (CDB CN : Z) (CD : list byte) (mI : mem) (zra zsp zgp ztp zs0 zs1 za2 za3 za4 za5 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs10 zs11 zt5 zt6 : word), NZ = 4 * Z.of_nat n -> forall
(rest done : list word) (x : word) (off kz r : Z) (yt1 yt2 yt3 yt4 : word) (F1 : bvmap 5 word) fc mc,
Q mod 4 = 0 -> aobj asegs mI Q NZ -> offsh [(Q, Q + NZ)] ->
aobj asegs mI CDB CN -> Z.of_nat (length CD) = CN -> u8ro asegs mc CDB CD -> CDB + CN <= Q ->
0 <= r -> r + Z.of_nat (S (length rest)) <= CN ->
off = 4 * Z.of_nat (length done) -> kz = Z.of_nat (S (length rest)) -> (length done + 1 + length rest = n)%nat ->
frm0 fc -> mem_inv asegs mc -> munch [(Q, Q + NZ)] mI mc -> wmono asegs mI mc ->
rw_cells asegs mc Q (f32 done) -> rw_cells asegs mc (Q + off) (f32 (x :: rest)) ->
evt asegs (scb_inner_post zra zsp zgp ztp zs0 zs1 za2 za3 za4 za5 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs10 zs11 zt5 zt6 Q NZ n mI)
(MS (mkR zra zsp zgp ztp (Z_to_bv 64 (Q + off)) yt1 yt2 zs0 zs1 (Z_to_bv 64 (Q + off)) (Z_to_bv 64 (CDB + r)) za2 za3 za4 za5 (Z_to_bv 64 (CDB + r)) (Z_to_bv 64 kz)
zs2 zs3 zs4 zs5 zs6 zs7 zs8 (Z_to_bv 64 SHB) zs10 zs11 yt3 yt4 zt5 zt6)
F1 (Z_to_bv 64 0xac964) fc None mc (seg_rom asegs)).
Proof.
intros Q NZ n CDB CN CD mI zra zsp zgp ztp zs0 zs1 za2 za3 za4 za5 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs10 zs11 zt5 zt6 ENZ rest.
induction rest as [|x' rest IH]; intros done x off kz r yt1 yt2 yt3 yt4 F1 fc mc Q4 OBQ OF OBC LCD RO SEP R0 R1 Hoff Hkz HN FRM MI MU WM DONE X;
pose proof OBQ as (OQ0 & OQ1 & _); pose proof OBC as (OC0 & OC1 & _); unfold APP_TOP in *;
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof (rw_cells_bound _ _ _ _ DONE) as BD; rewrite cells_size_f32 in BD;
subst kz.
- cbn [length] in HN, R1. rewrite f32_cons, f32_nil in X.
assert (NTH : nth_error CD (Z.to_nat r) = Some (nth (Z.to_nat r) CD (Z_to_bv 8 0))) by (apply nth_error_nth'; lia).
pose proof (u8ro_read asegs mc CDB CD r _ _ RO NTH ltac:(lia) eq_refl) as RD. clear NTH.
ato 0xac970. astep. chk_merge OBC 1.
ato 0xac984. astep. chk_merge OBQ 4.
ato 0xac990. astep. chk_merge OBQ 4.
ato 0xac9bc. astep. cbn [length].
try sh_if.
ato 0xac9f0.
chunk_snoc DONE X. rewrite f32_snoc in DONE.
unfold scb_inner_post. finish; [ exact DONE | ].
rewrite length_app. cbn [length]. lia.
- cbn [length] in HN, BX, R1.
rewrite f32_cons in X. chunk_uncons X as X1.
assert (NTH : nth_error CD (Z.to_nat r) = Some (nth (Z.to_nat r) CD (Z_to_bv 8 0))) by (apply nth_error_nth'; lia).
pose proof (u8ro_read asegs mc CDB CD r _ _ RO NTH ltac:(lia) eq_refl) as RD. clear NTH.
ato 0xac970. astep. chk_merge OBC 1.
ato 0xac984. astep. chk_merge OBQ 4.
ato 0xac990. astep. chk_merge OBQ 4.
ato 0xac9bc. astep. cbn [length].
sh_if.
chunk_snoc DONE X1. rewrite f32_snoc in DONE.
replace (Z.of_nat (S (S (length rest))) + -1) with (Z.of_nat (S (length rest))) by lia.
replace (Q + off + 4) with (Q + (off + 4)) in * by lia.
replace (CDB + r + 1) with (CDB + (r + 1)) by lia.
eapply (IH (done ++ [_]) x' (off + 4) _ (r + 1)); try eassumption; try reflexivity.
all: try (rewrite ?length_app; cbn [length] in *; lia).
Qed.

Definition scb_outer_post (zra zsp zgp ztp zs0 za3 za4 zs3 zs4 zs5 zs6 zs7 zs8 zs10 zs11 zt5 zt6 : word) (FB INN : Z) (mI : mem) : machine_state -> Prop :=
fun ms' => exists t0' t1' t2' a0' a1' a2' a5' a6' a7' s2' t3' t4' F' fc' m' (ws : list word),
ms' = MS (mkR zra zsp zgp ztp t0' t1' t2' zs0 (Z_to_bv 64 FB) a0' a1' a2' za3 za4 a5' a6' a7' s2' zs3 zs4 zs5 zs6 zs7 zs8 (Z_to_bv 64 SHB) zs10 zs11 t3' t4' zt5 zt6)
F' (Z_to_bv 64 0xaca28) fc' None m' (seg_rom asegs)
/\ munch [(INN, INN + 160)] mI m' /\ wmono asegs mI m' /\ mem_inv asegs m'
/\ frm0 fc' /\ rw_cells asegs m' INN (f32 ws) /\ length ws = 40%nat.

Lemma scb_outer : forall (SP FB IND SGN INN CDB ssz sbits nbz : Z) (CD : list byte) (mI : mem) (zra zsp zgp ztp zs0 zs6 zs7 zs8 zs10 zs11 : word),
FB = SP + 192 -> IND = SP + 128 -> SGN = SP + 32 -> SP mod 4 = 0 -> 0 <= SP -> SP + 384 < 2^63 ->
1 <= ssz <= 20 -> 1 <= sbits <= 8 -> 1 <= nbz <= 8 ->
INN mod 4 = 0 -> aobj asegs mI INN 160 -> offsh [(INN, INN + 160)] -> (INN + 160 <= SP \/ SP + 384 <= INN) ->
aobj asegs mI CDB (2 ^ sbits * ssz) -> Z.of_nat (length CD) = 2 ^ sbits * ssz -> CDB + 2 ^ sbits * ssz <= INN -> CDB + 2 ^ sbits * ssz <= SP ->
aobj asegs mI IND (4 * nbz) -> aobj asegs mI SGN (4 * nbz) ->
forall (irest srest : list word) (iw sw : word) (done rest : list word) (i off offi : Z) (yt0 yt1 yt2 ya0 ya1 ya6 ya7 yt3 yt4 : word) (F1 : bvmap 5 word) fc mc,
i + Z.of_nat (S (length irest)) = nbz -> 0 <= i -> offi = 4 * i -> length srest = length irest ->
off = 4 * Z.of_nat (length done) -> Z.of_nat (length rest) = ssz * Z.of_nat (S (length irest)) -> (length done + length rest = 40)%nat ->
Forall (wbnd (2 ^ sbits)) (iw :: irest) -> Forall (wbnd 2) (sw :: srest) ->
rw_cells asegs mc (FB + 48) [C8 (Z_to_bv 64 SGN)] ->
rw_cells asegs mc (IND + offi) (f32 (iw :: irest)) -> rw_cells asegs mc (SGN + offi) (f32 (sw :: srest)) ->
u8ro asegs mc CDB CD ->
rw_cells asegs mc INN (f32 done) -> rw_cells asegs mc (INN + off) (f32 rest) ->
frm0 fc -> mem_inv asegs mc -> munch [(INN, INN + 160)] mI mc -> wmono asegs mI mc ->
evt asegs (scb_outer_post zra zsp zgp ztp zs0 (Z_to_bv 64 (4 * ssz)) (Z_to_bv 64 0x236d8) (Z_to_bv 64 CDB) (Z_to_bv 64 nbz) (Z_to_bv 64 IND) zs6 zs7 zs8 zs10 zs11 (Z_to_bv 64 ssz) (Z_to_bv 64 ssz) FB INN mI)
(MS (mkR zra zsp zgp ztp yt0 yt1 yt2 zs0 (Z_to_bv 64 FB) ya0 ya1 (Z_to_bv 64 i) (Z_to_bv 64 (4 * ssz)) (Z_to_bv 64 0x236d8) (Z_to_bv 64 (INN + off)) ya6 ya7
(Z_to_bv 64 (INN + off)) (Z_to_bv 64 CDB) (Z_to_bv 64 nbz) (Z_to_bv 64 IND) zs6 zs7 zs8 (Z_to_bv 64 SHB) zs10 zs11 yt3 yt4 (Z_to_bv 64 ssz) (Z_to_bv 64 ssz))
F1 (Z_to_bv 64 0xac900) fc None mc (seg_rom asegs)).
Proof.
intros SP FB IND SGN INN CDB ssz sbits nbz CD mI zra zsp zgp ztp zs0 zs6 zs7 zs8 zs10 zs11 EFB EIND ESGN SP4 SP0 SPH HSS HSB HNB N4 OBN OF NAP OBC LCD SEPC SEPS OBI OBS irest.
pose proof OBN as (ON0 & ON1 & _). pose proof OBC as (OC0 & OC1 & _). unfold APP_TOP in *.
assert (I4 : IND mod 4 = 0) by (clear - EIND SP4; Z.div_mod_to_equations; lia).
assert (S4 : SGN mod 4 = 0) by (clear - ESGN SP4; Z.div_mod_to_equations; lia).
assert (P2 : 2 <= 2 ^ sbits <= 256).
{ clear - HSB. split; [change 2 with (2 ^ 1) at 1| change 256 with (2 ^ 8)]; apply Z.pow_le_mono_r; lia. }
hide_disj.
induction irest as [|iw' irest IH]; intros srest iw sw done rest i off offi yt0 yt1 yt2 ya0 ya1 ya6 ya7 yt3 yt4 F1 fc mc
Hi Hi0 Hoffi LSR Hoff LREST LTOT FI FS SLOT IX SX RO DONE REST FRM MI MU WM.
2:{
destruct srest as [|sw' srest]; [cbn [length] in LSR; lia|].
apply Forall_cons_iff in FI. destruct FI as ((iv & -> & IVR) & FI).
apply Forall_cons_iff in FS. destruct FS as ((sv & -> & SVR) & FS).
cbn [length] in Hi, LSR, LREST.
ato 0xac900. astep. sh_if.
ato 0xac90c. astep.
replace (Z.shiftl i 2) with offi by (rewrite Z.shiftl_mul_pow2 by lia; lia).
rewrite f32_cons in SX. chunk_uncons SX as SX1. rewrite f32_cons in IX. chunk_uncons IX as IX1.
ato 0xac91c. astep. chk_merge OBS 4.
ato 0xac934. astep. chk_merge OBI 4.
ato 0xac940.
rewrite (sx32_small iv) by (unfold int31; lia).
assert (SV : sv = 0 \/ sv = 1) by lia.
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mc _) =>
eapply (evt_cut segs (JX segs 0xac94c mc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _));
[ destruct SV as [-> | ->]; rewrite sx32_small by (unfold int31; lia); rewrite unsigned_small64 by lia;
[ change (Z.b2z (0 <? 1)) with 1 | change (Z.b2z (1 <? 1)) with 0 ]; ato 0xac94c; jx_done
| clear FRM; intros ? (? & ? & ? & -> & FRM) ]
end.
ato 0xac964.
rewrite swrap32_small by (clear - IVR HSS P2; nia).
assert (ROW : 0 <= iv * ssz /\ iv * ssz + ssz <= 2 ^ sbits * ssz) by (clear - IVR HSS P2; nia).
set (row := iv * ssz) in *. clearbody row. destruct ROW as (R0 & R1).
assert (REM0 : 0 <= ssz * Z.of_nat (length irest)) by (apply Z.mul_nonneg_nonneg; lia).
assert (KL : (Z.to_nat ssz <= length rest)%nat) by lia.
destruct (f32_split asegs _ (INN + off) rest (Z.to_nat ssz) KL REST) as (WIN & REST').
assert (LWIN : length (firstn (Z.to_nat ssz) rest) = Z.to_nat ssz) by (apply firstn_length_le; exact KL).
assert (LSKP : length (skipn (Z.to_nat ssz) rest) = (length rest - Z.to_nat ssz)%nat) by (apply length_skipn).
set (win := firstn (Z.to_nat ssz) rest) in *. set (rest' := skipn (Z.to_nat ssz) rest) in *. clearbody win rest'. clear REST.
destruct win as [|wx wr]; [cbn [length] in LWIN; lia|]. cbn [length] in LWIN.
replace (Z_to_bv 64 (INN + off)) with (Z_to_bv 64 (INN + off + 0)) by (rewrite Z.add_0_r; reflexivity).
replace (INN + off) with (INN + off + 0) in WIN at 1 by lia.
vloop_facts OBN MU OF INN (INN + off) (4 * ssz). vloop_cb OBC MU OF CDB (2 ^ sbits * ssz).
assert (OFW : offsh [(INN + off, INN + off + 4 * ssz)]).
{ clear - OF LTOT Hoff KL HSS. cbn in OF |- *. destruct OF as (O1 & _). split; [|exact I]. lia. }
rewrite Z2Nat.id in REST' by lia.
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mc _) =>
eapply evt_cut; [ eapply (scb_inner (INN + off) (4 * ssz) (Z.to_nat ssz) CDB (2 ^ sbits * ssz) CD mc) with (rest := wr) (done := []) (x := wx) (off := 0) (r := row) (kz := ssz)
| clear MU0 WM0 OBQc OBCc D0 OFW WIN FRM; post_call segs mc ]
end.
1: lia.
1: (clear - N4 Hoff; Z.div_mod_to_equations; lia).
1: exact OBQc. 1: exact OFW. 1: exact OBCc. 1: exact LCD. 1: exact RO. 1: lia. 1: exact R0. 1: lia.
1: reflexivity. 1: lia. 1: (cbn [length]; lia).
1: eassumption. 1: eassumption. 1: exact MU0. 1: exact WM0. 1: exact D0. 1: exact WIN.
match goal with H : rw_cells asegs _ (INN + off) (f32 ?l), L : length ?l = _, F : frm0 _ |- _ => rename H into WIN; rename L into LW; rename F into FRM end.
rewrite !Z.add_0_r.
ato 0xac9fc. astep. sh_if.
lazymatch type of WIN with rw_cells _ _ _ (f32 ?l) => rename l into ws end.
chunk_cat DONE WIN. rewrite <- f32_app in DONE.
replace (INN + off + 4 * ssz) with (INN + (off + 4 * ssz)) in * by lia.
replace (SGN + offi + 4) with (SGN + (offi + 4)) in * by lia. replace (IND + offi + 4) with (IND + (offi + 4)) in * by lia.
eapply (IH srest iw' sw' (done ++ ws) rest' (i + 1) (off + 4 * ssz) (offi + 4)).
1: lia. 1: lia. 1: lia. 1: lia.
1: (rewrite length_app, LW; lia).
1: lia.
1: (rewrite length_app; lia).
1: exact FI. 1: exact FS. 1: exact SLOT. 1: exact IX. 1: exact SX. 1: exact RO. 1: exact DONE. 1: exact REST'.
1: exact FRM. 1: assumption. 1: exact MU. 1: exact WM.
}
{
destruct srest as [|sw' srest]; [|cbn [length] in LSR; lia].
apply Forall_cons_iff in FI. destruct FI as ((iv & -> & IVR) & FI).
apply Forall_cons_iff in FS. destruct FS as ((sv & -> & SVR) & FS).
cbn [length] in Hi, LSR, LREST.
ato 0xac900. astep. sh_if.
ato 0xac90c. astep.
replace (Z.shiftl i 2) with offi by (rewrite Z.shiftl_mul_pow2 by lia; lia).
rewrite f32_cons, f32_nil in SX. rewrite f32_cons, f32_nil in IX.
ato 0xac91c. astep. chk_merge OBS 4.
ato 0xac934. astep. chk_merge OBI 4.
ato 0xac940.
rewrite (sx32_small iv) by (unfold int31; lia).
assert (SV : sv = 0 \/ sv = 1) by lia.
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mc _) =>
eapply (evt_cut segs (JX segs 0xac94c mc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _));
[ destruct SV as [-> | ->]; rewrite sx32_small by (unfold int31; lia); rewrite unsigned_small64 by lia;
[ change (Z.b2z (0 <? 1)) with 1 | change (Z.b2z (1 <? 1)) with 0 ]; ato 0xac94c; jx_done
| clear FRM; intros ? (? & ? & ? & -> & FRM) ]
end.
ato 0xac964.
rewrite swrap32_small by (clear - IVR HSS P2; nia).
assert (ROW : 0 <= iv * ssz /\ iv * ssz + ssz <= 2 ^ sbits * ssz) by (clear - IVR HSS P2; nia).
set (row := iv * ssz) in *. clearbody row. destruct ROW as (R0 & R1).
assert (KL : (Z.to_nat ssz <= length rest)%nat) by lia.
destruct (f32_split asegs _ (INN + off) rest (Z.to_nat ssz) KL REST) as (WIN & REST').
assert (LWIN : length (firstn (Z.to_nat ssz) rest) = Z.to_nat ssz) by (apply firstn_length_le; exact KL).
assert (LSKP : length (skipn (Z.to_nat ssz) rest) = (length rest - Z.to_nat ssz)%nat) by (apply length_skipn).
set (win := firstn (Z.to_nat ssz) rest) in *. set (rest' := skipn (Z.to_nat ssz) rest) in *. clearbody win rest'. clear REST.
destruct rest' as [|? ?]; [|cbn [length] in LSKP; lia]. clear REST'.
destruct win as [|wx wr]; [cbn [length] in LWIN; lia|]. cbn [length] in LWIN.
replace (Z_to_bv 64 (INN + off)) with (Z_to_bv 64 (INN + off + 0)) by (rewrite Z.add_0_r; reflexivity).
replace (INN + off) with (INN + off + 0) in WIN at 1 by lia.
vloop_facts OBN MU OF INN (INN + off) (4 * ssz). vloop_cb OBC MU OF CDB (2 ^ sbits * ssz).
assert (OFW : offsh [(INN + off, INN + off + 4 * ssz)]).
{ clear - OF LTOT Hoff KL HSS. cbn in OF |- *. destruct OF as (O1 & _). split; [|exact I]. lia. }
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mc _) =>
eapply evt_cut; [ eapply (scb_inner (INN + off) (4 * ssz) (Z.to_nat ssz) CDB (2 ^ sbits * ssz) CD mc) with (rest := wr) (done := []) (x := wx) (off := 0) (r := row) (kz := ssz)
| clear MU0 WM0 OBQc OBCc D0 OFW WIN FRM; post_call segs mc ]
end.
1: lia.
1: (clear - N4 Hoff; Z.div_mod_to_equations; lia).
1: exact OBQc. 1: exact OFW. 1: exact OBCc. 1: exact LCD. 1: exact RO. 1: lia. 1: exact R0. 1: lia.
1: reflexivity. 1: lia. 1: (cbn [length]; lia).
1: eassumption. 1: eassumption. 1: exact MU0. 1: exact WM0. 1: exact D0. 1: exact WIN.
match goal with H : rw_cells asegs _ (INN + off) (f32 ?l), L : length ?l = _, F : frm0 _ |- _ => rename H into WIN; rename L into LW; rename F into FRM end.
rewrite !Z.add_0_r.
ato 0xac9fc. astep. sh_if.
ato 0xaca28.
lazymatch type of WIN with rw_cells _ _ _ (f32 ?l) => rename l into ws end.
chunk_cat DONE WIN. rewrite <- f32_app in DONE.
unfold scb_outer_post. finish; [ exact DONE | ].
rewrite length_app. cbn [length] in LTOT. lia.
}
Qed.
