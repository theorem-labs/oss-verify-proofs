(* The personality pieces of the image-B walks of diginet_fader_encode, diginet_touch_encode and
   diginet_vpot_encode (lib/AU/Prog/CPgEncU.v), over lib/A/Prog/CPgBase.v's pers_argA / cpers_disj and the plumbing
   of lib/AU/Prog/CPgWalkU.v. The image-B form of lib/A/Prog/CPgEncPers.v: each lemma and tactic is the image-A one,
   over image B's core, and atom 10's fact in pers_AF carries p mod 8 = 0 (the contracts' premise), so the engine
   decides image B's UBSan check of the personality pointer's alignment (`andi _,p,7; bnez`); pers_atoms_ok takes that
   premise.
   Each of the three reads one byte of the personality, p->strips at p + 17, after the instrumented check of that byte,
   and only after it has loaded the shadow offset through the .got slot A_GOT_shadow and the cell A_shadow_glob.
   - at entry (pd = Some d) the state carries the atom facts pers_AF k (atom 10 = p in [1, PERS_HI], 8-aligned, atom
     k = the byte d_strips d) and the shadow-table entry pers_SH = mkSHE 10 16 20 (pers_shent); pers_some gives the Z
     facts of pers_argA;
   - at a stop after the two loads of the shadow offset, pers_swap_tac drops the regions of the two cells
     (cw_drop_gb) and adds pers_region k, the read-only byte p + 17 holding atom k (pers_add_at); pers_disj proves its
     extent goal, pers_off_zone places p + 17 off the save area and off out;
   - pd = None is p = 0 (pers_none_p); the first `beqz` on atom 10 is then taken (pers_beqz0), and with pd = Some d it
     is not (pers_beqz_some);
   - the unsigned compare of strip (an arg_u32A register) with the loaded byte is pers_strip_ltu. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
(* first, so that the engine's names (st_ok, ...) shadow the spec's *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkU.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ================================ the entry pieces ================================ *)
Definition PERS_HI : Z := 2 ^ 47 - 21.
Definition pers_SH : shent := mkSHE 10 16 20.
(* atom 10 = p: in [1, PERS_HI] and 8-aligned; atom k = the byte p->strips *)
Definition pers_AF (k : nat) : list (nat * afact) := [(10%nat, mkAF 1 PERS_HI 3); (k, mkAF 0 255 0)].
(* the byte p + 17 = p->strips, read-only, holding atom k *)
Definition pers_region (k : nat) : YP09.region :=
YP09.mkRegion (Some 10%nat) 17 18 0 0 [YP09.mkChunk 17 (CVal 1 (SOff k 0))].

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Lemma pers_none_p : forall segs B (W : world segs) memc sp T p, pers_argA segs B W memc sp T p None -> p = 0.
Proof. intros segs B W memc sp T p H. exact H. Qed.

Section c.
Variable B : asyms.
(* the Z facts of pers_argA (Some d) a walk uses *)
Lemma pers_some : forall (W : world tfibsegs) memc sp T p d,
pers_argA tfibsegs B W memc sp T p (Some d) ->
1 <= p <= PERS_HI /\ 0 <= d_strips d < 256 /\
val_mem tfibsegs (mrestrict (w_H W) memc) (p + 17) 1 (d_strips d) /\
(p + 20 <= sp - T \/ sp <= p + 16) /\ cimg_range tfibsegs B sp T (p + 16) 4.
Proof.
intros W memc sp T p d (Hp0 & Hp1 & Hdev & Hstr & Hch & Hcnt & HG & HC).
pose proof HC as (_ & _ & _ & Ham & Hwin & _ & _).
pose proof (garr8_nthZ tfibsegs _ _ _ 1 HG ltac:(lia) ltac:(cbn; lia)) as [Hv _].
change (nth (Z.to_nat 1) [d_dev d; d_strips d; d_chars d; d_counter d] 0) with (d_strips d) in Hv.
replace (p + 16 + 1) with (p + 17) in Hv by lia.
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham.
unfold coff_win in Hwin. unfold PERS_HI.
split; [lia|]. split; [exact Hstr|]. split; [exact Hv|]. split; [lia | exact HC].
Qed.

Lemma pers_atoms_ok : forall E (k : nat) p s, ew E 10 = Z_to_bv 64 p -> ew E k = Z_to_bv 64 s ->
1 <= p <= PERS_HI -> p mod 8 = 0 -> 0 <= s < 256 -> atoms_ok E (pers_AF k).
Proof.
intros E k p s H10 Hk Hp Hal Hs. unfold pers_AF. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite H10, Hk. unfold PERS_HI in *. rewrite !unsigned_lit_small by lia.
change (2 ^ 3) with 8. rewrite Z.pow_0_r, Z.mod_1_r. repeat split; first [exact Hal | lia].
Qed.

(* p + 17 is off the save area [sp - T, sp) and off the n bytes at out *)
Lemma pers_off_zone : forall (W : world tfibsegs) memc sp T p d out n,
pers_argA tfibsegs B W memc sp T p (Some d) -> cpers_disj (Some d) p out n ->
~ (sp - T <= p + 17 < sp) /\ ~ (out <= p + 17 < out + n).
Proof.
intros W memc sp T p d out n HP HD.
pose proof (pers_some W memc sp T p d HP) as (_ & _ & _ & Hwin & _).
cbn [cpers_disj] in HD. split; lia.
Qed.
(* the engine's shadow entry of p + 16 .. p + 19, from cimg_range's usable shadow at the state AR holds of *)
Lemma pers_shent : forall ly S (W : world tfibsegs) memc md sp T E p d,
AR tfibsegs B ly S W memc md -> pers_argA tfibsegs B W memc sp T p (Some d) ->
ew E 10 = Z_to_bv 64 p -> ew E 32 = Z_to_bv 64 SB ->
shent_ok tfibsegs CW_Bx E (mrestrict (w_H W) memc) pers_SH.
Proof.
intros ly S W memc md sp T E p d HAR HP E10 E32.
pose proof (pers_some W memc sp T p d HP) as (Hp & _ & _ & _ & HC).
exact (cw_shent_img_off B ly S W memc md sp T E 10 p 16 4 HAR HC E10 ltac:(lia) ltac:(lia) E32).
Qed.
End c.

(* ======================= the personality byte, added at a stop =======================
   The walk runs past the two loads of the shadow offset with CPgWalk's base regions, drops the .got slot and the
   cell (CPgWalk's cw_drop_gb), then adds the byte p + 17. *)
Lemma pers_add : forall E ss ms (k : nat) p s,
st_ok tfibsegs E ss ms ->
bv_unsigned (ew E 10) = p -> ew E k = Z_to_bv 64 s -> 0 <= s < 256 -> 0 <= p -> p + 18 <= 2 ^ 64 ->
val_mem tfibsegs (ms_mem ms) (p + 17) 1 s ->
all_disjoint E (pers_region k) (ss_mem ss) ->
st_ok tfibsegs E (mkSS (ss_pc ss) (ss_regs ss) (pers_region k :: ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms k p s HS Hp Hk Hs Hp0 Hp1 Hv Hd.
refine (ast_ok_add_region tfibsegs E ss ms (pers_region k) HS eq_refl _ Hd).
unfold region_ok. cbn [pers_region YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite Hp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val tfibsegs E _ p 17 1 (SOff k 0) s);
[cbn [sv_denot]; rewrite Hk, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| change (2 ^ (8 * Z.of_N 1)) with 256; lia | cbn; lia | exact Hv].
Qed.
(* the same at a stop of a walk, with the byte kept from the call's entry memory memc *)
Lemma pers_add_at : forall E ss (W : world tfibsegs) ms (k : nat) p s memc,
st_ok tfibsegs E ss (restrict (w_H W) ms) ->
bv_unsigned (ew E 10) = p -> ew E k = Z_to_bv 64 s ->
val_mem tfibsegs (mrestrict (w_H W) memc) (p + 17) 1 s ->
aview tfibsegs (w_H W) (ms_mem ms) (p + 17) = aview tfibsegs (w_H W) memc (p + 17) ->
0 <= s < 256 -> 0 <= p -> p + 18 <= 2 ^ 64 ->
all_disjoint E (pers_region k) (ss_mem ss) ->
st_ok tfibsegs E (mkSS (ss_pc ss) (ss_regs ss) (pers_region k :: ss_mem ss) (ss_resv ss) (ss_facts ss))
(restrict (w_H W) ms).
Proof.
intros E ss W ms k p s memc HS Hp Hk Hv Ha Hs Hp0 Hp1 Hd.
apply (pers_add E ss _ k p s HS Hp Hk Hs Hp0 Hp1); [|exact Hd].
apply (cw_val_mem_kept (w_H W) (w_H W) memc (ms_mem ms) (p + 17) 1 s); [|exact Hv].
intros x Hx. replace x with (p + 17) by lia. exact Ha.
Qed.
End b.
(* an atom of the walk's base env read through the ewset / havoc layers the runs put over it *)
Ltac pers_ew_base := rewrite ?ew_ewset_other, ?ew_havoc_old by (cbn; lia).
(* At a stop after the two loads of the shadow offset: HS : st_ok tfibsegs E ss (restrict (w_H W) ms) loses the .got
   slot and the cell (cw_drop_gb) and gains the byte p + 17, with its region list computed. E10 : ew E0 10 = Z_to_bv
   64 p and Ek : ew E0 k = Z_to_bv 64 s hold of the walk's base env E0, Hv is the byte at the entry memory memc
   (pers_some), kept proves `aview tfibsegs (w_H W) (ms_mem ms) (p + 17) = aview tfibsegs (w_H W) memc (p + 17)`
   (from the walk's KE), the bounds 0 <= s < 256 and 1 <= p <= PERS_HI are in context, and disj proves the extent
   goal (pers_disj below). *)
Ltac pers_swap_tac E10 Ek Hv kept disj :=
cw_drop_gb;
lazymatch goal with HS : st_ok tfibsegs ?E ?ss (restrict (w_H ?W) ?ms) |- _ =>
lazymatch type of E10 with ew _ 10 = Z_to_bv 64 ?p =>
lazymatch type of Ek with ew _ ?k = Z_to_bv 64 ?s =>
lazymatch type of Hv with val_mem tfibsegs (mrestrict (w_H W) ?memc) _ _ _ =>
let Hp := fresh "Hp" in let Hk := fresh "Hk" in let Ha := fresh "Ha" in let HS' := fresh "HS" in
assert (Hp : bv_unsigned (ew E 10) = p) by (pers_ew_base; rewrite E10; apply unsigned_lit_small; unfold PERS_HI in *; lia);
assert (Hk : ew E k = Z_to_bv 64 s) by (pers_ew_base; exact Ek);
assert (Ha : aview tfibsegs (w_H W) (ms_mem ms) (p + 17) = aview tfibsegs (w_H W) memc (p + 17)) by kept;
pose proof (pers_add_at E ss W ms k p s memc HS Hp Hk Hv Ha) as HS';
specialize (HS' ltac:(lia) ltac:(lia) ltac:(unfold PERS_HI in *; lia));
lazymatch type of HS' with ?D -> _ => let HD := fresh "HD" in assert (HD : D) by disj; specialize (HS' HD); clear HD end;
clear HS Hp Hk Ha;
lazymatch type of HS' with st_ok _ _ ?ss2 _ =>
let ss3 := eval vm_compute in ss2 in change (st_ok tfibsegs E ss3 (restrict (w_H W) ms)) in HS' end;
rename HS' into HS
end end end end.
(* the extent goal: the region list computed, each base read in the walk's base env through the run layers, by
   the hypotheses `bv_unsigned (ew _ n) = _` or `ew _ n = Z_to_bv 64 _` in context, then lia *)
Ltac pers_disj :=
idtac; lazymatch goal with |- all_disjoint ?E ?r ?rs =>
let rs' := eval vm_compute in rs in change (all_disjoint E r rs') end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [pers_region YP09.r_base YP09.r_lo YP09.r_hi base_val];
pers_ew_base;
repeat match goal with
| H : bv_unsigned (ew ?E0 ?n) = _ |- context [bv_unsigned (ew ?E0 ?n)] => rewrite H
| H : ew ?E0 ?n = Z_to_bv 64 _ |- context [bv_unsigned (ew ?E0 ?n)] => rewrite H, unsigned_lit_small by (unfold PERS_HI in *; lia)
end;
repeat split; lia.

(* ================================ branch and compare facts ================================ *)
(* `beqz` on atom 10 (the first test of each of the three) *)
Lemma pers_beqz0 : forall E, ew E 10 = Z_to_bv 64 0 ->
branch_taken BC_EQ (sv_denot E (SOff 10 0)) (sv_denot E (SLit 0)) = true.
Proof. intros E H. rewrite branch_eq_U, (U_atom E 10 0 H), U_lit by lia. reflexivity. Qed.
Lemma pers_beqz_some : forall E p, ew E 10 = Z_to_bv 64 p -> 1 <= p < 2 ^ 64 ->
branch_taken BC_EQ (sv_denot E (SOff 10 0)) (sv_denot E (SLit 0)) = false.
Proof. intros E p H Hp. rewrite branch_eq_U, (U_atom E 10 p H), U_lit by lia. apply Z.eqb_neq. lia. Qed.
(* the register of an arg_u32A v, read unsigned *)
Lemma pers_U_u32 : forall E n v, ew E n = w64 (DgnLib.s32 v) -> 0 <= v < 2 ^ 32 ->
U E (SOff n 0) = if v <? 2 ^ 31 then v else v + (2 ^ 64 - 2 ^ 32).
Proof.
intros E n v H Hv. unfold w64, DgnLib.s32 in H. revert H. destruct (Z.ltb_spec v (2 ^ 31)) as [Hlt|Hge]; intros H.
- rewrite (cw_U_offx E n v 0 H) by lia. rewrite Z.add_0_r. apply Z.mod_small. lia.
- assert (H' : ew E n = Z_to_bv 64 (v + (2 ^ 64 - 2 ^ 32))).
  { rewrite H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    replace (v + (2 ^ 64 - 2 ^ 32)) with (v - 2 ^ 32 + 1 * 2 ^ 64) by lia. rewrite Z.mod_add by lia. reflexivity. }
  rewrite (cw_U_offx E n _ 0 H') by lia. rewrite Z.add_0_r. apply Z.mod_small. lia.
Qed.
(* the loaded byte, zero-extended or as the atom *)
Lemma pers_U_byte : forall E (k : nat) s, ew E k = Z_to_bv 64 s -> 0 <= s < 256 ->
U E (SExt false 8 (SOff k 0)) = s /\ U E (SOff k 0) = s.
Proof.
intros E k s H Hs. rewrite U_zext, (U_atom E k s H) by lia. change (2 ^ Z.of_N 8) with 256.
split; [apply Z.mod_small; lia | reflexivity].
Qed.
(* `bltu` / `bgeu` of strip (a1 or any arg_u32A register) against the byte x = s *)
Lemma pers_strip_ltu : forall E n v x s, ew E n = w64 (DgnLib.s32 v) -> 0 <= v < 2 ^ 32 ->
U E x = s -> 0 <= s < 256 ->
(U E (SOff n 0) <? U E x) = (v <? s).
Proof.
intros E n v x s H Hv Hx Hs. rewrite (pers_U_u32 E n v H Hv), Hx.
destruct (Z.ltb_spec v (2 ^ 31)); [reflexivity|].
destruct (Z.ltb_spec (v + (2 ^ 64 - 2 ^ 32)) s); destruct (Z.ltb_spec v s); first [reflexivity | lia].
Qed.
