(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Reals Lra.
From Flocq Require Import Core.Raux Core.Defs.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s YK0p.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ0a YQ05 YQ0e YQ02 YQ00 YQ07 YQ08.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 YI00 YI02 YI01 YI03 YI07
UI1e UI1i YI0x YP14 YI08 YI0c YI0f YI0d UI3h UI3j UI3k.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YM00 YM07 YM05 YM04 YM01 YM02 YM06.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN07.
Ltac2 sat_vars () := [@API; @STK; @sp0; @FP; @L; @A; @mem0; @md0; @L2; @A2; @md2; @regs0; @palp; @frp; @nln; @imin; @imax; @cidx; @res; @pal; @fr].
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Local Abbreviation D := fmt_double.
Section e. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section f.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Local Notation segs := ubs2segs.
Local Notation rom := (seg_rom ubs2segs).
Variables (STK sp0 : Z) (FP : list (Z * Z)) (L : layout) (A : astate) (mem0 : word -> option byte) (md0 : Model).
Variables (L2 : layout) (A2 : astate) (md2 : Model).
Variables (regs0 : bvmap 5 word) (palp frp nln imin imax cidx res : Z) (pal fr : list Z).
Local Notation spc := (spZ regs0 - 160).
Hypothesis Hii : 0 <= imin <= imax.
Hypothesis Himax : imax < 2 ^ 30.
Hypothesis Hlenp : 3 * (imax + 1) <= zlen pal.
Hypothesis Hlenf : imax + 1 <= zlen fr.
Hypothesis Hpalv : forall j, (j < length pal)%nat -> 0 <= nth j pal 0 < 256.
Hypothesis Hfrv : forall j, (j < length fr)%nat -> 0 <= nth j fr 0 < 2 ^ 32.
Hypothesis Hfr1 : forall i, imin <= i <= imax -> 1 <= getz fr i.
Hypothesis Hsum : wsum (node_list pal fr imin imax 0) <= RGB_NMAX.
Hypothesis Hpalp : 4096 <= palp. Hypothesis Hpalhi : palp + zlen pal <= alloc_ceiling.
Hypothesis Hfrp : 4096 <= frp. Hypothesis Hfrhi : frp + 4 * zlen fr <= alloc_ceiling. Hypothesis Hfr4 : frp mod 4 = 0.
Hypothesis Hpfd : palp + zlen pal <= frp \/ frp + 4 * zlen fr <= palp.
Hypothesis Hres0 : 4096 <= res. Hypothesis Hres1 : res + NODE_SIZE <= alloc_ceiling. Hypothesis Hres16 : res mod 16 = 0.
Hypothesis Hnp : res + NODE_SIZE <= palp \/ palp + zlen pal <= res. Hypothesis Hnf : res + NODE_SIZE <= frp \/ frp + 4 * zlen fr <= res.
Hypothesis Hbud : sp0 - STK <= spZ regs0 - NTN_STK. Hypothesis Hsptop : spZ regs0 <= sp0. Hypothesis Hal16 : spZ regs0 mod 16 = 0.
Hypothesis Hceil : alloc_ceiling + STK <= sp0. Hypothesis H63 : sp0 < 2 ^ 63.
Lemma ntn_consts : NODE_SIZE = 56 /\ NTN_STK = 160 + ALLOC_STACK /\ ALLOC_STACK = 8192 /\ RGB_NMAX = 10000 /\ (CEIL_MIN <= alloc_ceiling <= CEIL_MAX)  .
Proof. repeat match goal with H : _ |- _ => clear H end.   pose proof (proj1 alloc_ceiling_val). repeat split; first [reflexivity | lia]. Qed.
Local Ltac ntn_wr HU2 :=
wr_ok_eval; eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo]; lia | cbn [r_whi]; lia |];
repeat (apply wr_ok_cons_ro; [cbn; lia|]); apply wr_ok_nil.
Let l0 := node_list pal fr imin imax 0. Let l1 := node_list pal fr imin imax 1. Let l2 := node_list pal fr imin imax 2.
Lemma splits_iff : forall d,
(exists a b, In a (node_list pal fr imin imax d) /\ In b (node_list pal fr imin imax d) /\ snd a <> snd b) <->
dim_splits pal imin imax d.
Proof.
intros d. split.
- intros (a & b & Ha & Hb & Hne). apply In_node_list in Ha as (i & Hi & ->). apply In_node_list in Hb as (j & Hj & ->).
cbn [snd] in Hne. exists i, j. auto.
- intros (i & j & Hi & Hj & Hne). exists (getz fr i, getz pal (3 * i + d)), (getz fr j, getz pal (3 * j + d)).
split; [apply In_node_list; exists i; auto|]. split; [apply In_node_list; exists j; auto|]. exact Hne.
Qed.
Lemma var_value : forall d xs xv, 0 <= d <= 2 ->
is_intd xs (wsum l0) ->
vacc xv (imax + 1 - imin) (neq_meanb (wsum (node_list pal fr imin imax d)) (wdot (node_list pal fr imin imax d)) (node_list pal fr imin imax d)) ->
exists v, dval (fst (fp_div D RNE xv xs)) v /\ (0 <= v)%R /\ ((0 < v)%R <-> dim_splits pal imin imax d).
Proof.
intros d xs xv Hd Hxs Hv. pose proof ntn_consts as (_ & _ & _ & HNM & _).
set (l := node_list pal fr imin imax d) in *.
assert (Hok : node_ok l) by (subst l; rewrite <- nlp_full; apply (nlp_node_ok pal fr imin imax Hii Hpalv Hfr1 Hlenp); lia).
assert (Hlen : Z.of_nat (length l) = imax - imin + 1) by (subst l; apply node_list_length; lia).
assert (Hne : l <> []) by (intros Hnil; rewrite Hnil in Hlen; cbn in Hlen; lia).
assert (Hws : wsum l <= 2 ^ 32).
{ subst l. rewrite <- nlp_full. pose proof (wsum_nlp_le pal fr imin imax Hii Hfr1 Hsum (imax + 1) d ltac:(lia)). rewrite HNM in *. lia. }
assert (Hxs' : is_intd xs (wsum l)).
{ subst l l0. rewrite <- nlp_full, (wsum_nlp_dim pal fr imin (imax + 1) d 0), nlp_full. exact Hxs. }
replace (imax + 1 - imin) with (Z.of_nat (length l)) in Hv by lia.
destruct (variance_sign xv xs l Hok Hne Hws ltac:(lia) Hv Hxs') as (v & Hdv & Hv0 & Hiff).
exists v. split; [exact Hdv|]. split; [exact Hv0|]. rewrite Hiff. apply splits_iff.
Qed.
Lemma VA_pick : forall xs xv0 xv1 xv2 (b1 b2 b3 : bool),
is_intd xs (wsum l0) ->
vacc xv0 (imax + 1 - imin) (neq_meanb (wsum l0) (wdot l0) l0) ->
vacc xv1 (imax + 1 - imin) (neq_meanb (wsum l1) (wdot l1) l1) ->
vacc xv2 (imax + 1 - imin) (neq_meanb (wsum l2) (wdot l2) l2) ->
let w0 := fst (fp_div D RNE xv0 xs) in let w1 := fst (fp_div D RNE xv1 xs) in let w2 := fst (fp_div D RNE xv2 xs) in
fst (fp_lt D 0 w0) = b1 ->
fst (fp_lt D (if b1 then w0 else 0) w1) = b2 ->
fst (fp_lt D (if b2 then w1 else if b1 then w0 else 0) w2) = b3 ->
range_has_two pal imin imax -> dim_splits pal imin imax (if b3 then 2 else if b2 then 1 else 0).
Proof.
intros xs xv0 xv1 xv2 b1 b2 b3 Hxs V0 V1 V2 w0 w1 w2 C1 C2 C3 Hr2.
destruct (var_value 0 xs xv0 ltac:(lia) Hxs V0) as (v0 & D0 & P0 & I0).
destruct (var_value 1 xs xv1 ltac:(lia) Hxs V1) as (v1 & D1 & P1 & I1).
destruct (var_value 2 xs xv2 ltac:(lia) Hxs V2) as (v2 & D2 & P2 & I2).
fold w0 in D0. fold w1 in D1. fold w2 in D2.
assert (HP : forall v, (0 <= v)%R -> if Rlt_bool 0 v then (0 < v)%R else v = 0%R).
{ intros v Hv. destruct (Rlt_bool_spec 0 v); lra. }
pose proof (argmax_pick w0 w1 w2 v0 v1 v2 (Rlt_bool 0 v0) (Rlt_bool 0 v1) (Rlt_bool 0 v2) b1 b2 b3
D0 D1 D2 P0 P1 P2 (HP v0 P0) (HP v1 P1) (HP v2 P2) C1 C2 C3) as HA.
assert (Hex : Rlt_bool 0 v0 = true \/ Rlt_bool 0 v1 = true \/ Rlt_bool 0 v2 = true).
{ destruct (range_has_two_dim pal imin imax Hr2) as (d & Hd & Hsp).
assert (Hd3 : d = 0 \/ d = 1 \/ d = 2) by lia.
destruct Hd3 as [-> | [-> | ->]];
[ left; apply Rlt_bool_true; apply I0; exact Hsp
| right; left; apply Rlt_bool_true; apply I1; exact Hsp
| right; right; apply Rlt_bool_true; apply I2; exact Hsp ]. }
specialize (HA Hex).
destruct b3; [|destruct b2];
[ apply I2; destruct (Rlt_bool_spec 0 v2); [lra | discriminate HA]
| apply I1; destruct (Rlt_bool_spec 0 v1); [lra | discriminate HA]
| apply I0; destruct (Rlt_bool_spec 0 v0); [lra | discriminate HA] ].
Qed.
Definition VA_post (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : config -> Prop :=
fun c' => exists (fy' : FPState) regs' mem' (cut : Z),
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 NT_TAIL) mem' rom) md2 /\
journal ubs2_msyms MR STK sp0 FP L A mem0 md0 L2 A2 mem' md2 /\ frm_zero (@fp_csr fy') /\
getr regs' 15 = Z_to_bv 64 cut /\ 0 <= cut <= 2 /\
(range_has_two pal imin imax -> dim_splits pal imin imax cut) /\
(forall r : reg, In r VA_KEEP -> getr regs' r = getr regs r) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spc + 80 <= a < spc + 104) -> mbyte segs mem' a = mbyte segs mem a).
Local Ltac flt_cond Hc Dat A32 A33 A34 A35 :=
apply flt_taken in Hc; rewrite ?sv_fmv_d in Hc; rewrite ?val_fdiv, ?denot_lit0 in Hc;
rewrite ?(Dat 32%nat _ A32), ?(Dat 33%nat _ A33), ?(Dat 34%nat _ A34), ?(Dat 35%nat _ A35) in Hc.
Local Ltac va_leaf HS HE HU2 Hpick :=
lazymatch type of HS with st_okF _ ?E1 ?ss1 ?ms1 =>
rewrite (st_okF_mkst segs E1 ss1 ms1 HS eq_refl); cbn [ss_pc];
apply SR_ret;
pose proof (st_okF_regs_kept segs E1 ss1 ms1 _ VA_KEEP HS ltac:(intros r _; apply HE; pose proof (u5_range r); unfold ridx; lia) ltac:(vm_compute; reflexivity)) as Hk;
pose proof (st_okF_reg segs E1 ss1 ms1 15%bv HS) as Hq15;
match type of Hq15 with _ = sv_denot _ ?v => let v' := eval vm_compute in v in change v with v' in Hq15 end;
cbn [sv_denot] in Hq15;
lazymatch type of Hq15 with _ = Z_to_bv 64 (zcanon ?c) =>
change (zcanon c) with c in Hq15;
exists (fp_of ms1), (ms_regs ms1), (ms_mem ms1), c
| _ = Z_to_bv 64 ?c =>
exists (fp_of ms1), (ms_regs ms1), (ms_mem ms1), c
end;
split; [reflexivity|]; split; [assumption|]; split; [exact (st_okF_frm segs E1 _ _ HS)|];
split; [exact Hq15|]; split; [lia|]; split; [exact Hpick|]; split; [exact Hk|];
intros a Ha Hna; mb_frames ltac:(exact Ha) ltac:(rewrite ?HU2; lia); reflexivity
end.
Lemma ntn_va : forall (fy : FPState) (regs : bvmap 5 word) mem (xs xv0 xv1 xv2 : Z),
journal ubs2_msyms MR STK sp0 FP L A mem0 md0 L2 A2 mem md2 ->
frm_zero (@fp_csr fy) ->
getr regs 2 = Z_to_bv 64 spc ->
val_mem segs mem (spc + 8) 8 xs -> val_mem segs mem (spc + 16) 8 xs -> val_mem segs mem (spc + 24) 8 xs ->
val_mem segs mem (spc + 32) 8 xv0 -> val_mem segs mem (spc + 40) 8 xv1 -> val_mem segs mem (spc + 48) 8 xv2 ->
0 <= xs < 2 ^ 64 -> 0 <= xv0 < 2 ^ 64 -> 0 <= xv1 < 2 ^ 64 -> 0 <= xv2 < 2 ^ 64 ->
is_intd xs (wsum l0) ->
vacc xv0 (imax + 1 - imin) (neq_meanb (wsum l0) (wdot l0) l0) ->
vacc xv1 (imax + 1 - imin) (neq_meanb (wsum l1) (wdot l1) l1) ->
vacc xv2 (imax + 1 - imin) (neq_meanb (wsum l2) (wdot l2) l2) ->
SR segs (mkCfg (@mkst fy regs (Z_to_bv 64 NT_VA) mem rom) md2) (VA_post fy regs mem).
Proof.
intros fy regs mem xs xv0 xv1 xv2 HJ Hfrm Hr2 V8 V16 V24 V32 V40 V48 Rs R0 R1 R2 Is Hv0 Hv1 Hv2.
pose proof ntn_consts as (HNS & HNTN & HAS & HNM & Hac).
pose proof HJ as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & Hstw) & _).
ltac2:(satvl VA_entry using (sat_vars ()) as LEM1); destruct (LEM1 fy regs mem xs xv0 xv1 xv2 Hfrm Hr2 V8 V16 V24 V32 V40 V48 Rs R0 R1 R2 ltac:(intros a Ha; apply Hstw; lia)) as (HS & HE & HEf & A32 & A33 & A34 & A35 & HU2).
set (E := ew_fregs _ 64 _) in HS, HE, HEf, A32, A33, A34, A35, HU2.
assert (Dat : forall n v, bv_unsigned (ew E n) = v -> bv_unsigned (sv_denot E (SOff n 0)) = v).
{ intros n v H. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact H. }
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 NT_VA) mem rom)) in HJ.
jrunF_to LAWS ubs2tbl_ok HS HJ NT_TAIL. { ntn_wr HU2. }
cbn [ms_mem mkst] in HF, HJ.
jbranchF ubs2tbl HS; flt_cond Hc Dat A32 A33 A34 A35.
- jrunF_to LAWS ubs2tbl_ok HS HJ NT_TAIL. { ntn_wr HU2. }
cbn [ms_mem mkst] in HF0, HJ.
jbranchF ubs2tbl HS; flt_cond Hc0 Dat A32 A33 A34 A35.
+ jrunF_to LAWS ubs2tbl_ok HS HJ NT_TAIL. { ntn_wr HU2. }
cbn [ms_mem mkst] in HF1, HJ.
jbranchF ubs2tbl HS; flt_cond Hc1 Dat A32 A33 A34 A35.
* jrunF_to LAWS ubs2tbl_ok HS HJ NT_TAIL. { ntn_wr HU2. }
cbn [ms_mem mkst] in HF2, HJ.
pose proof (VA_pick xs xv0 xv1 xv2 true true true Is Hv0 Hv1 Hv2 Hc Hc0 Hc1) as Hpick.
va_leaf HS HE HU2 Hpick.
* jrunF_to LAWS ubs2tbl_ok HS HJ NT_TAIL. { ntn_wr HU2. }
cbn [ms_mem mkst] in HF2, HJ.
pose proof (VA_pick xs xv0 xv1 xv2 true true false Is Hv0 Hv1 Hv2 Hc Hc0 Hc1) as Hpick.
va_leaf HS HE HU2 Hpick.
+ jrunF_to LAWS ubs2tbl_ok HS HJ NT_TAIL. { ntn_wr HU2. }
cbn [ms_mem mkst] in HF1, HJ.
jbranchF ubs2tbl HS; flt_cond Hc1 Dat A32 A33 A34 A35.
* jrunF_to LAWS ubs2tbl_ok HS HJ NT_TAIL. { ntn_wr HU2. }
cbn [ms_mem mkst] in HF2, HJ.
pose proof (VA_pick xs xv0 xv1 xv2 true false true Is Hv0 Hv1 Hv2 Hc Hc0 Hc1) as Hpick.
va_leaf HS HE HU2 Hpick.
* jrunF_to LAWS ubs2tbl_ok HS HJ NT_TAIL. { ntn_wr HU2. }
cbn [ms_mem mkst] in HF2, HJ.
pose proof (VA_pick xs xv0 xv1 xv2 true false false Is Hv0 Hv1 Hv2 Hc Hc0 Hc1) as Hpick.
va_leaf HS HE HU2 Hpick.
- jrunF_to LAWS ubs2tbl_ok HS HJ NT_TAIL. { ntn_wr HU2. }
cbn [ms_mem mkst] in HF0, HJ.
jbranchF ubs2tbl HS; flt_cond Hc0 Dat A32 A33 A34 A35.
+ jrunF_to LAWS ubs2tbl_ok HS HJ NT_TAIL. { ntn_wr HU2. }
cbn [ms_mem mkst] in HF1, HJ.
jbranchF ubs2tbl HS; flt_cond Hc1 Dat A32 A33 A34 A35.
* jrunF_to LAWS ubs2tbl_ok HS HJ NT_TAIL. { ntn_wr HU2. }
cbn [ms_mem mkst] in HF2, HJ.
pose proof (VA_pick xs xv0 xv1 xv2 false true true Is Hv0 Hv1 Hv2 Hc Hc0 Hc1) as Hpick.
va_leaf HS HE HU2 Hpick.
* jrunF_to LAWS ubs2tbl_ok HS HJ NT_TAIL. { ntn_wr HU2. }
cbn [ms_mem mkst] in HF2, HJ.
pose proof (VA_pick xs xv0 xv1 xv2 false true false Is Hv0 Hv1 Hv2 Hc Hc0 Hc1) as Hpick.
va_leaf HS HE HU2 Hpick.
+ jrunF_to LAWS ubs2tbl_ok HS HJ NT_TAIL. { ntn_wr HU2. }
cbn [ms_mem mkst] in HF1, HJ.
jbranchF ubs2tbl HS; flt_cond Hc1 Dat A32 A33 A34 A35.
* jrunF_to LAWS ubs2tbl_ok HS HJ NT_TAIL. { ntn_wr HU2. }
cbn [ms_mem mkst] in HF2, HJ.
pose proof (VA_pick xs xv0 xv1 xv2 false false true Is Hv0 Hv1 Hv2 Hc Hc0 Hc1) as Hpick.
va_leaf HS HE HU2 Hpick.
* jrunF_to LAWS ubs2tbl_ok HS HJ NT_TAIL. { ntn_wr HU2. }
cbn [ms_mem mkst] in HF2, HJ.
pose proof (VA_pick xs xv0 xv1 xv2 false false false Is Hv0 Hv1 Hv2 Hc Hc0 Hc1) as Hpick.
va_leaf HS HE HU2 Hpick.
Qed.
End f.
End e.
