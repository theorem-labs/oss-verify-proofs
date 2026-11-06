(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1dg.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.PA Require Import X1e9 X1e5.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0j2 X0hi X0j3 X03z X04v X0jg X00b X046.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X04r X04t X04l X04u X04q X04o.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X19l X183 X19m X0ux X0vt X19x X0ra X0v4.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0vp X0vr X0vj X0vs X0vo X0vm.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X183 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ux OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0vt OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v4.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0vp OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0vr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0vj OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0vs OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0vo OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0vm.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Local Definition zal (k x r : Z) : Prop := (x mod k = r)%Z.
Local Lemma zal_ex : forall k x r : Z, (0 < k)%Z -> (x mod k = r)%Z -> exists q, x = (k * q + r)%Z.
Proof. intros k x r Hk H. exists (x / k)%Z. rewrite <- H. apply Z.div_mod. lia. Qed.
Local Ltac zlit x := lazymatch x with Zpos _ => idtac | Z0 => idtac | Zneg _ => idtac end.
Local Ltac zget_mod t :=
lazymatch type of t with
| (?x mod ?k = ?r)%Z => let H' := fresh "Hzm" in pose proof t as H'
| ?A /\ ?B => first [ zget_mod constr:(proj1 t) | zget_mod constr:(proj2 t) ]
end.
Local Ltac zhide :=
repeat match goal with
| H : context [(?x mod ?k)%Z] |- _ => zlit x; zlit k; let v := eval cbv in (x mod k)%Z in change (x mod k)%Z with v in H
end;
repeat match goal with
| H : (?x mod ?k = ?r)%Z |- _ =>
let q := fresh "zq" in let Hq := fresh "Hzq" in
destruct (zal_ex k x r (eq_refl : (0 < k)%Z) H) as [q Hq]; change (zal k x r) in H
| H : context [(?x mod ?k = ?r)%Z] |- _ =>
lazymatch type of H with (_ mod _ = _)%Z => fail | _ => idtac end;
(try zget_mod H); change (x mod k = r)%Z with (zal k x r) in H
end;
repeat match goal with
| H : context [(2 ^ ?k)%Z] |- _ => let T := type of H in zify_arith_prop T;
let v := eval cbv in (2 ^ k)%Z in lazymatch v with Zpos _ => change (2 ^ k)%Z with v in H end
end.

Local Definition zidle (P : Prop) : Prop := P.
Local Ltac zidle1 H := let T := type of H in change (zidle T) in H.
Local Ltac zidle_nsp H A sp := lazymatch A with context [bv_unsigned sp] => fail | _ => zidle1 H end.
Local Ltac zidle_begin sp n MUz WMz :=
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
pose proof (munch_refl [(bv_unsigned sp - n, bv_unsigned sp)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
repeat match goal with
| H : rw_cells segs m ?A _ |- _ => zidle_nsp H A sp
| H : ro_cells segs m ?A _ |- _ => zidle_nsp H A sp
| H : u8arr segs m ?A _ |- _ => zidle_nsp H A sp
| H : u32arr segs m ?A _ |- _ => zidle_nsp H A sp
| H : u64arr segs m ?A _ |- _ => zidle_nsp H A sp
| H : bytes_at segs m ?A _ |- _ => zidle_nsp H A sp
| H : u8ro segs m ?A _ |- _ => zidle_nsp H A sp
end
end.
Local Ltac zidle_end MUz WMz :=
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
lazymatch type of MUz with munch _ ?m _ =>
try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.

Local Ltac zidle_end_m m :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
unfold zidle in *; transport_after_call bsegs m mm MU WM end end.

Definition pfcells (m : mem) : Prop :=
rw_cells bsegs m 0x106798 [C1 (Z_to_bv 8 1)]
/\ ro_cells bsegs m 0xfc108 [C8 (Z_to_bv 64 0x1975e8)]
/\ ro_cells bsegs m 0x19763c [C1 (Z_to_bv 8 1)]
/\ ro_cells bsegs m 0xfdf28 [C8 (Z_to_bv 64 0xf1040)]
/\ ro_cells bsegs m 0xfdf30 [C8 (Z_to_bv 64 0xedf30)].
Definition in_PFR (x : Z) : Prop :=
(0x106798 <= x < 0x106799) \/ (0xfc108 <= x < 0xfc110) \/ (0x19763c <= x < 0x19763d) \/ (0xfdf28 <= x < 0xfdf38).

Lemma pfcells_munch : forall W m m', pfcells m -> munch W m m' -> wmono bsegs m m' ->
(forall x, in_PFR x -> outside W x) -> pfcells m'.
Proof.
intros W m m' (X1 & X2 & X3 & X4 & X5) MU WM HW.
pose proof (agree_of_munch W m m' _ MU HW) as AG.
assert (RO : forall A cs, ro_cells bsegs m A cs -> (forall x, A <= x < A + Z.of_nat (cells_size cs) -> in_PFR x) ->
ro_cells bsegs m' A cs).
{ intros A cs H HX. apply (ro_cells_agree bsegs m m' _ _ H). apply (agree_sub _ _ _ _ AG). exact HX. }
assert (RW : forall A cs, rw_cells bsegs m A cs -> (forall x, A <= x < A + Z.of_nat (cells_size cs) -> in_PFR x) ->
rw_cells bsegs m' A cs).
{ intros A cs H HX. apply (rw_cells_agree bsegs m m' _ _ H); [| exact WM].
apply (agree_sub _ _ _ _ AG). exact HX. }
split; [| split; [| split; [| split]]].
all: first [ apply RW; [assumption| cbn [cells_size csize]; intros x Hx; unfold in_PFR; lia]
| apply RO; [assumption| cbn [cells_size csize]; intros x Hx; unfold in_PFR; lia] ].
Qed.

Section WithRIP.
Hypothesis RIP : rip_stmt.

Definition vpwA_post (usp ap : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists (m' : mem) (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (junk : list byte),
ms' = MS (mkR (Z_to_bv 64 0x5a190) (Z_to_bv 64 (usp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 0x1529e) (Z_to_bv 64 0x1008a0)
(Z_to_bv 64 0x1008a0) (Z_to_bv 64 0x1529e) (Z_to_bv 64 ap) a3 a4 a5 a6 a7 (Z_to_bv 64 ap) s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6)
F (Z_to_bv 64 0xedf30) fc None m' (seg_rom bsegs)
/\ munch [(usp - 2416, usp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (usp + -96)
/\ rw_cells bsegs m' (usp + -96) [C8 (Z_to_bv 64 ap); C8 (Z_to_bv 64 ap); C8 s2; C8 (Z_to_bv 64 ap); C8 (Z_to_bv 64 0x1529e);
C8 (Z_to_bv 64 0x59620)]
/\ rw_cells bsegs m' (usp + -48) [CB 8 junk; C8 (Z_to_bv 64 ap); C8 (Z_to_bv 64 ap); C8 s1; C8 s0; C8 ra].

Lemma vprintf_walkA : forall (usp ap lo : Z)
ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
stk bsegs m lo usp -> lo <= usp - 2416 -> kHighShadowEnd + 8 <= lo -> usp <= 2^47 -> usp mod 16 = 0 -> 0 <= ap < 2^63 ->
chk_ok m 0x1529e 4 -> pctx m -> pfcells m -> mem_inv bsegs m ->
evt bsegs (vpwA_post usp ap ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x1529e) (Z_to_bv 64 ap) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x56cfc) fc None m (seg_rom bsegs)).
Proof using RIP.
intros until m. intros ST LO LOLO SPH S16 AP0 CHK PCX PFC MI.
unfold kHighShadowEnd in LOLO.
pose proof (munch_refl [(usp - 2416, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
assert (EU48 : bv_unsigned (Z_to_bv 64 (usp + -48)) = usp + -48) by (apply unsigned_lit; lia).
assert (EU96 : bv_unsigned (Z_to_bv 64 (usp + -96)) = usp + -96) by (apply unsigned_lit; lia).
destruct PFC as (AI & GCF & CPF & RVP & RVF).
carve_frame 48%nat ST. rename FR into FRv.
apply (rw_cells_split_CB bsegs _ _ [] 48 _ [] [8; 8; 8; 8; 8; 8]%nat) in FRv; [| reflexivity]. cbn [mk_CB_cells app] in FRv.
zhide.
xsteps_to 0x6f79c%Z.
call try_init_spec; [exact AI | rewrite EU48; exact ST | rewrite EU48; lia | lia | assumption |].
xsteps_to 0x59658%Z.
rename POST into ST.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
assert (CHK1 : chk_ok mm 0x1529e 4) by
(eapply chk_ok_agree; [exact CHK | lia | lia | apply (agree_of_munch _ _ _ _ MU); intros ?x ?Hx; cbn [outside]; unfold SHB in *; lia]);
assert (PCX1 : pctx mm) by
(apply (pctx_munch _ m mm PCX MU); [assumption| intros ?x ?Hx; unfold in_PCR in Hx; cbn [outside]; lia]) end.
call (pcom_emit_spec RIP);
[ reflexivity | reflexivity | exact ST | rewrite EU48; lia | (unfold kHighShadowEnd; lia) | rewrite EU48; lia
| rewrite EU48; Z.div_mod_to_equations; lia | lia | exact CHK1 | exact PCX1 | assumption | ].
clear CHK1 PCX1. rename POST into ST. rewrite EU48 in ST.
carve_frame 48%nat ST. rename FR into FRf.
apply (rw_cells_split_CB bsegs _ _ [] 48 _ [] [8; 8; 8; 8; 8; 8]%nat) in FRf; [| reflexivity]. cbn [mk_CB_cells app] in FRf.
xsteps_to 0x6f79c%Z.
call try_init_spec; [exact AI | rewrite EU96; exact ST | rewrite EU96; lia | lia | assumption |].
xsteps_to 0x59658%Z.
rename POST into ST.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
assert (CHK1 : chk_ok mm 0x1529e 4) by
(eapply chk_ok_agree; [exact CHK | lia | lia | apply (agree_of_munch _ _ _ _ MU); intros ?x ?Hx; cbn [outside]; unfold SHB in *; lia]);
assert (PCX1 : pctx mm) by
(apply (pctx_munch _ m mm PCX MU); [assumption| intros ?x ?Hx; unfold in_PCR in Hx; cbn [outside]; lia]) end.
call (pcom_emit_spec RIP);
[ reflexivity | reflexivity | exact ST | rewrite EU96; lia | (unfold kHighShadowEnd; lia) | rewrite EU96; lia
| rewrite EU96; Z.div_mod_to_equations; lia | lia | exact CHK1 | exact PCX1 | assumption | ].
clear CHK1 PCX1. rename POST into ST. rewrite EU96 in ST.
xsteps_to 0xedf30%Z.
apply evt_done. unfold vpwA_post. do 14 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FRf| exact FRv].
Qed.
End WithRIP.

Lemma vprintf_walkB : forall (usp ap lo : Z) (junk : list byte)
(ra' ra gp tp t0 t1 t2 s0 s1 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2 s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem),
stk bsegs m lo (usp + -96) -> lo <= usp + -96 -> usp <= 2^47 ->
rw_cells bsegs m (usp + -96) [C8 (Z_to_bv 64 ap); C8 (Z_to_bv 64 ap); C8 s2; C8 (Z_to_bv 64 ap); C8 (Z_to_bv 64 0x1529e);
C8 (Z_to_bv 64 0x59620)] ->
rw_cells bsegs m (usp + -48) [CB 8 junk; C8 (Z_to_bv 64 ap); C8 (Z_to_bv 64 ap); C8 s1; C8 s0; C8 ra] ->
mem_inv bsegs m ->
evt bsegs (fun ms' => (exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0' t1' t2' s0 s1 a0 a1' a2' a3' a4' a5' a6' a7'
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m (seg_rom bsegs))
/\ stk bsegs m lo usp)
(MS (mkR ra' (Z_to_bv 64 (usp + -96)) gp tp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x5a190) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros ST LO UT FRf FRv MI.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (EU96 : bv_unsigned (Z_to_bv 64 (usp + -96)) = usp + -96) by (apply unsigned_lit; lia).
assert (EU48 : bv_unsigned (Z_to_bv 64 (usp + -48)) = usp + -48) by (apply unsigned_lit; lia).
zhide.
do 6 lstep.
release_frame FRf ST (usp + -48).
do 5 lstep.
release_frame FRv ST usp.
apply evt_done. split; [| exact ST]. do 14 eexists. first [reflexivity | f_equal; f_equal; apply Z_to_bv_eqm; lia].
Qed.
End B_TWIN.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Local Definition zal (k x r : Z) : Prop := (x mod k = r)%Z.
Local Lemma zal_ex : forall k x r : Z, (0 < k)%Z -> (x mod k = r)%Z -> exists q, x = (k * q + r)%Z.
Proof. intros k x r Hk H. exists (x / k)%Z. rewrite <- H. apply Z.div_mod. lia. Qed.
Local Ltac zlit x := lazymatch x with Zpos _ => idtac | Z0 => idtac | Zneg _ => idtac end.
Local Ltac zget_mod t :=
lazymatch type of t with
| (?x mod ?k = ?r)%Z => let H' := fresh "Hzm" in pose proof t as H'
| ?A /\ ?B => first [ zget_mod constr:(proj1 t) | zget_mod constr:(proj2 t) ]
end.
Local Ltac zhide :=
repeat match goal with
| H : context [(?x mod ?k)%Z] |- _ => zlit x; zlit k; let v := eval cbv in (x mod k)%Z in change (x mod k)%Z with v in H
end;
repeat match goal with
| H : (?x mod ?k = ?r)%Z |- _ =>
let q := fresh "zq" in let Hq := fresh "Hzq" in
destruct (zal_ex k x r (eq_refl : (0 < k)%Z) H) as [q Hq]; change (zal k x r) in H
| H : context [(?x mod ?k = ?r)%Z] |- _ =>
lazymatch type of H with (_ mod _ = _)%Z => fail | _ => idtac end;
(try zget_mod H); change (x mod k = r)%Z with (zal k x r) in H
end;
repeat match goal with
| H : context [(2 ^ ?k)%Z] |- _ => let T := type of H in zify_arith_prop T;
let v := eval cbv in (2 ^ k)%Z in lazymatch v with Zpos _ => change (2 ^ k)%Z with v in H end
end.

Local Definition zidle (P : Prop) : Prop := P.
Local Ltac zidle1 H := let T := type of H in change (zidle T) in H.
Local Ltac zidle_nsp H A sp := lazymatch A with context [bv_unsigned sp] => fail | _ => zidle1 H end.
Local Ltac zidle_begin sp n MUz WMz :=
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
pose proof (munch_refl [(bv_unsigned sp - n, bv_unsigned sp)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
repeat match goal with
| H : rw_cells segs m ?A _ |- _ => zidle_nsp H A sp
| H : ro_cells segs m ?A _ |- _ => zidle_nsp H A sp
| H : u8arr segs m ?A _ |- _ => zidle_nsp H A sp
| H : u32arr segs m ?A _ |- _ => zidle_nsp H A sp
| H : u64arr segs m ?A _ |- _ => zidle_nsp H A sp
| H : bytes_at segs m ?A _ |- _ => zidle_nsp H A sp
| H : u8ro segs m ?A _ |- _ => zidle_nsp H A sp
end
end.
Local Ltac zidle_end MUz WMz :=
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
lazymatch type of MUz with munch _ ?m _ =>
try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.

Local Ltac zidle_end_m m :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
unfold zidle in *; transport_after_call asegs m mm MU WM end end.

Definition pfcells (m : mem) : Prop :=
rw_cells asegs m 0xfdf58 [C1 (Z_to_bv 8 1)]
/\ ro_cells asegs m 0xf3888 [C8 (Z_to_bv 64 0x18eda8)]
/\ ro_cells asegs m 0x18edfc [C1 (Z_to_bv 8 1)]
/\ ro_cells asegs m 0xf56a8 [C8 (Z_to_bv 64 0xe87cc)]
/\ ro_cells asegs m 0xf56b0 [C8 (Z_to_bv 64 0xe56bc)].
Definition in_PFR (x : Z) : Prop :=
(0xfdf58 <= x < 0xfdf59) \/ (0xf3888 <= x < 0xf3890) \/ (0x18edfc <= x < 0x18edfd) \/ (0xf56a8 <= x < 0xf56b8).

Lemma pfcells_munch : forall W m m', pfcells m -> munch W m m' -> wmono asegs m m' ->
(forall x, in_PFR x -> outside W x) -> pfcells m'.
Proof.
intros W m m' (X1 & X2 & X3 & X4 & X5) MU WM HW.
pose proof (agree_of_munch W m m' _ MU HW) as AG.
assert (RO : forall A cs, ro_cells asegs m A cs -> (forall x, A <= x < A + Z.of_nat (cells_size cs) -> in_PFR x) ->
ro_cells asegs m' A cs).
{ intros A cs H HX. apply (ro_cells_agree asegs m m' _ _ H). apply (agree_sub _ _ _ _ AG). exact HX. }
assert (RW : forall A cs, rw_cells asegs m A cs -> (forall x, A <= x < A + Z.of_nat (cells_size cs) -> in_PFR x) ->
rw_cells asegs m' A cs).
{ intros A cs H HX. apply (rw_cells_agree asegs m m' _ _ H); [| exact WM].
apply (agree_sub _ _ _ _ AG). exact HX. }
split; [| split; [| split; [| split]]].
all: first [ apply RW; [assumption| cbn [cells_size csize]; intros x Hx; unfold in_PFR; lia]
| apply RO; [assumption| cbn [cells_size csize]; intros x Hx; unfold in_PFR; lia] ].
Qed.

Section WithRIP.
Hypothesis RIP : rip_stmt.

Definition vpwA_post (usp ap : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists (m' : mem) (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (junk : list byte),
ms' = MS (mkR (Z_to_bv 64 0x5a0a4) (Z_to_bv 64 (usp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 0x151ae) (Z_to_bv 64 0xf8020)
(Z_to_bv 64 0xf8020) (Z_to_bv 64 0x151ae) (Z_to_bv 64 ap) a3 a4 a5 a6 a7 (Z_to_bv 64 ap) s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6)
F (Z_to_bv 64 0xe56bc) fc None m' (seg_rom asegs)
/\ munch [(usp - 2416, usp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (usp + -96)
/\ rw_cells asegs m' (usp + -96) [C8 (Z_to_bv 64 ap); C8 (Z_to_bv 64 ap); C8 s2; C8 (Z_to_bv 64 ap); C8 (Z_to_bv 64 0x151ae);
C8 (Z_to_bv 64 0x59534)]
/\ rw_cells asegs m' (usp + -48) [CB 8 junk; C8 (Z_to_bv 64 ap); C8 (Z_to_bv 64 ap); C8 s1; C8 s0; C8 ra].

Lemma vprintf_walkA : forall (usp ap lo : Z)
ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
stk asegs m lo usp -> lo <= usp - 2416 -> kHighShadowEnd + 8 <= lo -> usp <= 2^47 -> usp mod 16 = 0 -> 0 <= ap < 2^63 ->
chk_ok m 0x151ae 4 -> pctx m -> pfcells m -> mem_inv asegs m ->
evt asegs (vpwA_post usp ap ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x151ae) (Z_to_bv 64 ap) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x56c10) fc None m (seg_rom asegs)).
Proof using RIP.
intros until m. intros ST LO LOLO SPH S16 AP0 CHK PCX PFC MI.
unfold kHighShadowEnd in LOLO.
pose proof (munch_refl [(usp - 2416, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
assert (EU48 : bv_unsigned (Z_to_bv 64 (usp + -48)) = usp + -48) by (apply unsigned_lit; lia).
assert (EU96 : bv_unsigned (Z_to_bv 64 (usp + -96)) = usp + -96) by (apply unsigned_lit; lia).
destruct PFC as (AI & GCF & CPF & RVP & RVF).
carve_frame 48%nat ST. rename FR into FRv.
apply (rw_cells_split_CB asegs _ _ [] 48 _ [] [8; 8; 8; 8; 8; 8]%nat) in FRv; [| reflexivity]. cbn [mk_CB_cells app] in FRv.
zhide.
xsteps_to 0x6f6b0%Z.
call try_init_spec; [exact AI | rewrite EU48; exact ST | rewrite EU48; lia | lia | assumption |].
xsteps_to 0x5956c%Z.
rename POST into ST.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
assert (CHK1 : chk_ok mm 0x151ae 4) by
(eapply chk_ok_agree; [exact CHK | lia | lia | apply (agree_of_munch _ _ _ _ MU); intros ?x ?Hx; cbn [outside]; unfold SHB in *; lia]);
assert (PCX1 : pctx mm) by
(apply (pctx_munch _ m mm PCX MU); [assumption| intros ?x ?Hx; unfold in_PCR in Hx; cbn [outside]; lia]) end.
call (pcom_emit_spec RIP);
[ reflexivity | reflexivity | exact ST | rewrite EU48; lia | (unfold kHighShadowEnd; lia) | rewrite EU48; lia
| rewrite EU48; Z.div_mod_to_equations; lia | lia | exact CHK1 | exact PCX1 | assumption | ].
clear CHK1 PCX1. rename POST into ST. rewrite EU48 in ST.
carve_frame 48%nat ST. rename FR into FRf.
apply (rw_cells_split_CB asegs _ _ [] 48 _ [] [8; 8; 8; 8; 8; 8]%nat) in FRf; [| reflexivity]. cbn [mk_CB_cells app] in FRf.
xsteps_to 0x6f6b0%Z.
call try_init_spec; [exact AI | rewrite EU96; exact ST | rewrite EU96; lia | lia | assumption |].
xsteps_to 0x5956c%Z.
rename POST into ST.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
assert (CHK1 : chk_ok mm 0x151ae 4) by
(eapply chk_ok_agree; [exact CHK | lia | lia | apply (agree_of_munch _ _ _ _ MU); intros ?x ?Hx; cbn [outside]; unfold SHB in *; lia]);
assert (PCX1 : pctx mm) by
(apply (pctx_munch _ m mm PCX MU); [assumption| intros ?x ?Hx; unfold in_PCR in Hx; cbn [outside]; lia]) end.
call (pcom_emit_spec RIP);
[ reflexivity | reflexivity | exact ST | rewrite EU96; lia | (unfold kHighShadowEnd; lia) | rewrite EU96; lia
| rewrite EU96; Z.div_mod_to_equations; lia | lia | exact CHK1 | exact PCX1 | assumption | ].
clear CHK1 PCX1. rename POST into ST. rewrite EU96 in ST.
xsteps_to 0xe56bc%Z.
apply evt_done. unfold vpwA_post. do 14 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FRf| exact FRv].
Qed.
End WithRIP.

Lemma vprintf_walkB : forall (usp ap lo : Z) (junk : list byte)
(ra' ra gp tp t0 t1 t2 s0 s1 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2 s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem),
stk asegs m lo (usp + -96) -> lo <= usp + -96 -> usp <= 2^47 ->
rw_cells asegs m (usp + -96) [C8 (Z_to_bv 64 ap); C8 (Z_to_bv 64 ap); C8 s2; C8 (Z_to_bv 64 ap); C8 (Z_to_bv 64 0x151ae);
C8 (Z_to_bv 64 0x59534)] ->
rw_cells asegs m (usp + -48) [CB 8 junk; C8 (Z_to_bv 64 ap); C8 (Z_to_bv 64 ap); C8 s1; C8 s0; C8 ra] ->
mem_inv asegs m ->
evt asegs (fun ms' => (exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0' t1' t2' s0 s1 a0 a1' a2' a3' a4' a5' a6' a7'
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m (seg_rom asegs))
/\ stk asegs m lo usp)
(MS (mkR ra' (Z_to_bv 64 (usp + -96)) gp tp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x5a0a4) fc None m (seg_rom asegs)).
Proof.
intros until m. intros ST LO UT FRf FRv MI.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (EU96 : bv_unsigned (Z_to_bv 64 (usp + -96)) = usp + -96) by (apply unsigned_lit; lia).
assert (EU48 : bv_unsigned (Z_to_bv 64 (usp + -48)) = usp + -48) by (apply unsigned_lit; lia).
zhide.
do 6 lstep.
release_frame FRf ST (usp + -48).
do 5 lstep.
release_frame FRv ST usp.
apply evt_done. split; [| exact ST]. do 14 eexists. first [reflexivity | f_equal; f_equal; apply Z_to_bv_eqm; lia].
Qed.
